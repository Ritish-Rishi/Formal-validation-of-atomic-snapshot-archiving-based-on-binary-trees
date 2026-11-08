------------------------ MODULE SnapArchTree_Search ------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS Threads, Components, MaxClock, MaxNodes, Values, Bot, Null

CompIdx(c) == CHOOSE i \in 1..Cardinality(Components) :
    Cardinality({x \in Components : x <= c}) = i

MaxHeap == Cardinality(Components) * (MaxNodes + 4 * Cardinality(Threads) + 6)

\* -------------------------------------------------------------------------
\* BITWISE PATHFINDING SIMULATOR
\* -------------------------------------------------------------------------
RECURSIVE GetPath(_)
GetPath(n) == IF n <= 1 THEN <<>> 
              ELSE Append(GetPath(n \div 2), IF n % 2 = 0 THEN "L" ELSE "R")

RECURSIVE FindNodeH(_, _, _, _)
FindNodeH(h, currPtr, pathSeq, idxStep) == 
    IF currPtr = Null \/ idxStep > Len(pathSeq) THEN currPtr
    ELSE IF pathSeq[idxStep] = "L" THEN FindNodeH(h, h[currPtr].left, pathSeq, idxStep + 1)
    ELSE FindNodeH(h, h[currPtr].right, pathSeq, idxStep + 1)

(* --algorithm SnapArchTree_Physical
variables
    COUNT = 0,
    c_val = [c \in Components |-> CHOOSE v \in Values : TRUE],
    c_nodeCount = [c \in Components |-> 1],
    c_deleted = [c \in Components |-> FALSE],
    
    \* Sequential ground-truth history log for verifying SearchTree linearizability
    history = [c \in Components |-> [t \in 0..MaxClock |-> IF t = 0 THEN {Bot, CHOOSE v \in Values : TRUE} ELSE {CHOOSE v \in Values : TRUE}]],
    
    \* Per-process return flags for procedures
    success = [p \in Threads \cup {"r1", "e1", "d1", "l1"} |-> FALSE],
    searchRet = [p \in Threads \cup {"r1", "e1", "d1", "l1"} |-> Bot],
    
    \* THE PHYSICAL MEMORY POOL
    heap = [i \in 1..MaxHeap |-> 
        IF i <= Cardinality(Components) 
        THEN [val |-> Bot, snapNum |-> 0, left |-> Null, right |-> Null]
        ELSE [val |-> Bot, snapNum |-> -1, left |-> Null, right |-> Null]],
    freePtr = Cardinality(Components) + 1,
    rootPtr = [c \in Components |-> CompIdx(c)];

define
    GetPhysicalNode(c, idx) == FindNodeH(heap, rootPtr[c], GetPath(idx), 1)
end define;

\* -------------------------------------------------------------------------
\* PROCEDURE: CatchUpTree with getNodeByIndex Traversal & Cooperative Helping
\* -------------------------------------------------------------------------
procedure CatchUpTreeProc(comp) 
variables 
    k = 1, lastPtr = Null, cnt = 0, liveVal = Bot, targetIdx = 0, 
    newNode = Null, parentIdx = 0, path = <<>>, curr = Null, loopStep = 1;
begin
CatchUp_Check:
    if c_deleted[comp] = TRUE then
        success[self] := TRUE;
        goto CatchUp_End;
    else
        k := c_nodeCount[comp];
        lastPtr := GetPhysicalNode(comp, k);
        if lastPtr /= Null /\ COUNT <= heap[lastPtr].snapNum then
            success[self] := TRUE;
            goto CatchUp_End;
        end if;
    end if;

CatchUp_SetTarget:
    liveVal := c_val[comp];
    cnt := COUNT;
    targetIdx := k + 1;
    if targetIdx > MaxNodes \/ freePtr > MaxHeap then
        goto CatchUp_End;
    elsif cnt <= heap[lastPtr].snapNum then
        success[self] := TRUE;
        goto CatchUp_End;
    else
        parentIdx := targetIdx \div 2;
        path := GetPath(parentIdx);
        curr := rootPtr[comp];
        loopStep := 1;
    end if;

CatchUp_GetNode_Loop:
    while loopStep <= Len(path) /\ curr /= Null do
        if path[loopStep] = "L" then
            curr := heap[curr].left;
        else
            curr := heap[curr].right;
        end if;
        loopStep := loopStep + 1;
    end while;

CatchUp_Alloc:
    if curr = Null then
        success := FALSE;
        goto CatchUp_End;
    elsif (targetIdx % 2 = 0 /\ heap[curr].left /= Null) \/ (targetIdx % 2 /= 0 /\ heap[curr].right /= Null) then
        if c_nodeCount[comp] = k then
            c_nodeCount[comp] := targetIdx;
        end if;
        goto CatchUp_Check;
    elsif liveVal /= c_val[comp] then
        goto CatchUp_Check;
    elsif freePtr > MaxHeap then      \* <-- new branch
        success := FALSE;
        goto CatchUp_End;
    else
        newNode := freePtr;
        freePtr := freePtr + 1;
        heap[newNode] := [val |-> liveVal, snapNum |-> cnt, left |-> Null, right |-> Null];
    end if;

CatchUp_CAS:
    if c_nodeCount[comp] = k /\ cnt > heap[lastPtr].snapNum then
        if targetIdx % 2 = 0 then
            if heap[curr].left = Null then
                heap[curr].left := newNode;
                success[self] := TRUE;
            else
                success[self] := FALSE;
            end if;
        else
            if heap[curr].right = Null then
                heap[curr].right := newNode;
                success[self] := TRUE;
            else
                success[self] := FALSE;
            end if;
        end if;
    else
        success[self] := FALSE;
    end if;

CatchUp_End:
    if curr /= Null then
        if (targetIdx % 2 = 0 /\ heap[curr].left /= Null) \/ (targetIdx % 2 /= 0 /\ heap[curr].right /= Null) then
            if c_nodeCount[comp] = k then
                c_nodeCount[comp] := targetIdx;
            end if;
        end if;
    end if;
    return;
end procedure;

\* -------------------------------------------------------------------------
\* PROCEDURE: SearchTree (Least-Upper-Bound Binary Search over [2 .. high])
\* -------------------------------------------------------------------------
procedure SearchTreeProc(comp, targetSnap)
variables 
    low = 2, high = 0, mid = 0, midPtr = Null, 
    closestMatchVal = Bot,
    path = <<>>, curr = Null, loopStep = 1;
begin
Search_Init:
    if c_deleted[comp] = TRUE then
        searchRet[self] := -99;
        goto Search_End;
    elsif targetSnap <= heap[rootPtr[comp]].snapNum then
        searchRet[self] := Bot;
        goto Search_End;
    else
        if GetPhysicalNode(comp, c_nodeCount[comp] + 1) /= Null then
            high := c_nodeCount[comp] + 1;
        else
            high := c_nodeCount[comp];
        end if;
        low := 2;
        closestMatchVal := c_val[comp];
        searchRet[self] := c_val[comp];
    end if;

Search_Loop:
    while low <= high do
        mid := low + ((high - low) \div 2);
        path := GetPath(mid);
        curr := rootPtr[comp];
        loopStep := 1;
        
        Search_Walk:
        while loopStep <= Len(path) /\ curr /= Null do
            if path[loopStep] = "L" then
                curr := heap[curr].left;
            else
                curr := heap[curr].right;
            end if;
            loopStep := loopStep + 1;
        end while;
        
        Search_Eval:
        midPtr := curr;
        if midPtr = Null then
            high := mid - 1;
        else
            if heap[midPtr].snapNum >= targetSnap then
                closestMatchVal := heap[midPtr].val;
                high := mid - 1;
            else
                low := mid + 1;
            end if;
        end if;
    end while;
    searchRet[self] := closestMatchVal;

Search_End:
    return;
end procedure;

process Client \in Threads
variables 
    targetComp = CHOOSE c \in Components : TRUE, 
    newVal = CHOOSE v \in Values : TRUE, 
    ops = 0;
begin
ClientLoop:
    while ops < 3 do
        ops := ops + 1;
        either
            ClickOp:
                if COUNT < MaxClock then 
                    COUNT := COUNT + 1;
                    history := [c \in Components |-> [history[c] EXCEPT ![COUNT] = {c_val[c]}]];
                end if;
        or
            Update_Select:
                with c \in Components do
                    targetComp := c;
                    newVal := IF ops = 2 THEN (CHOOSE v \in Values : TRUE) 
                              ELSE (CHOOSE v \in Values : v /= (CHOOSE v2 \in Values : TRUE) \/ Cardinality(Values) = 1);
                end with;
            Update_Catchup:
                call CatchUpTreeProc(targetComp);
            Update_RetryCatchup:
                if ~success[self] then
                    call CatchUpTreeProc(targetComp);
                end if;
            Update_Apply:
                if c_deleted[targetComp] = FALSE then
                    c_val[targetComp] := newVal;
                    history[targetComp][COUNT] := history[targetComp][COUNT] \cup {newVal};
                end if;
        end either;
    end while;
end process;

process Reader = "r1"
variables 
    searchComp = CHOOSE c \in Components : TRUE,
    targetSnapshot \in {0, MaxClock},
    finalResult = Bot;
begin
Reader_Start:
    await COUNT >= 2 \/ (\A t \in Threads : pc[t] = "Done");
    if targetSnapshot > heap[GetPhysicalNode(searchComp, c_nodeCount[searchComp])].snapNum then
        call CatchUpTreeProc(searchComp);
    end if;
Reader_RetryHelp:
    if targetSnapshot > heap[GetPhysicalNode(searchComp, c_nodeCount[searchComp])].snapNum then
        call CatchUpTreeProc(searchComp);
    end if;
Reader_InvokeSearch:
    call SearchTreeProc(searchComp, targetSnapshot);
Reader_Finish:
    finalResult := searchRet["r1"];
end process;

\* Models Algorithm 5: Bounded-Prefix Global Snapshot and BFS Tree Extraction
process Exporter = "e1"
variables 
    expComp = CHOOSE c \in Components : TRUE,
    snapBoundary = 0,
    exportLimit = 0,
    bfsQueue = <<>>,
    visitedCount = 0,
    currExportPtr = Null,
    exportedSnaps = <<>>,
    exportedVals = <<>>;
begin
Export_Start:
    await pc["r1"]="Done"/\(\A t \in Threads : pc[t]="Done");
    if COUNT < MaxClock then
        COUNT := COUNT + 1;
        history := [c \in Components |-> [history[c] EXCEPT ![COUNT] = {c_val[c]}]];
    end if;
    snapBoundary := COUNT;
    if c_deleted[expComp] = FALSE then
        call CatchUpTreeProc(expComp);
    end if;
Export_SecondCatchUp:
    if c_deleted[expComp] = FALSE /\ ~success["e1"] then
        call CatchUpTreeProc(expComp);
    end if;
Export_InitBFS:
    if c_deleted[expComp] = FALSE then
        exportLimit := c_nodeCount[expComp];
        if rootPtr[expComp] /= Null /\ exportLimit >= 1 then
            bfsQueue := <<rootPtr[expComp]>>;
            visitedCount := 0;
        end if;
    end if;
Export_BFSLoop:
    while Len(bfsQueue) > 0 /\ visitedCount < exportLimit do
        currExportPtr := Head(bfsQueue);
        visitedCount := visitedCount + 1;
        if visitedCount > 1 then
            exportedSnaps := Append(exportedSnaps, heap[currExportPtr].snapNum);
            exportedVals := Append(exportedVals, heap[currExportPtr].val);
        end if;
        bfsQueue := Tail(bfsQueue)
                    \o (IF heap[currExportPtr].left /= Null THEN <<heap[currExportPtr].left>> ELSE <<>>)
                    \o (IF heap[currExportPtr].right /= Null THEN <<heap[currExportPtr].right>> ELSE <<>>);
    end while;
end process;

process Deleter = "d1"
variables delComp = CHOOSE c \in Components : TRUE;
begin
Delete_Await:
    await pc["e1"]="Done";
Delete_Execute:
    c_deleted[delComp] := TRUE;
end process;

process LiveReader = "l1"
variables liveComp = CHOOSE c \in Components : TRUE, liveResult = Bot;
begin
Check_Alive:
    await pc["e1"]="Done";
    if c_deleted[liveComp] = TRUE then
        liveResult := -99;
    else
        liveResult := c_val[liveComp];
    end if;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2c66bba2" /\ chksum(tla) = "e0ee30bf")
\* Procedure variable path of procedure CatchUpTreeProc at line 56 col 36 changed to path_
\* Procedure variable curr of procedure CatchUpTreeProc at line 56 col 49 changed to curr_
\* Procedure variable loopStep of procedure CatchUpTreeProc at line 56 col 62 changed to loopStep_
\* Parameter comp of procedure CatchUpTreeProc at line 53 col 27 changed to comp_
CONSTANT defaultInitValue
VARIABLES COUNT, c_val, c_nodeCount, c_deleted, history, success, searchRet, 
          heap, freePtr, rootPtr, pc, stack

(* define statement *)
GetPhysicalNode(c, idx) == FindNodeH(heap, rootPtr[c], GetPath(idx), 1)

VARIABLES comp_, k, lastPtr, cnt, liveVal, targetIdx, newNode, parentIdx, 
          path_, curr_, loopStep_, comp, targetSnap, low, high, mid, midPtr, 
          closestMatchVal, path, curr, loopStep, targetComp, newVal, ops, 
          searchComp, targetSnapshot, finalResult, expComp, snapBoundary, 
          exportLimit, bfsQueue, visitedCount, currExportPtr, exportedSnaps, 
          exportedVals, delComp, liveComp, liveResult

vars == << COUNT, c_val, c_nodeCount, c_deleted, history, success, searchRet, 
           heap, freePtr, rootPtr, pc, stack, comp_, k, lastPtr, cnt, liveVal, 
           targetIdx, newNode, parentIdx, path_, curr_, loopStep_, comp, 
           targetSnap, low, high, mid, midPtr, closestMatchVal, path, curr, 
           loopStep, targetComp, newVal, ops, searchComp, targetSnapshot, 
           finalResult, expComp, snapBoundary, exportLimit, bfsQueue, 
           visitedCount, currExportPtr, exportedSnaps, exportedVals, delComp, 
           liveComp, liveResult >>

ProcSet == (Threads) \cup {"r1"} \cup {"e1"} \cup {"d1"} \cup {"l1"}

Init == (* Global variables *)
        /\ COUNT = 0
        /\ c_val = [c \in Components |-> CHOOSE v \in Values : TRUE]
        /\ c_nodeCount = [c \in Components |-> 1]
        /\ c_deleted = [c \in Components |-> FALSE]
        /\ history = [c \in Components |-> [t \in 0..MaxClock |-> IF t = 0 THEN {Bot, CHOOSE v \in Values : TRUE} ELSE {CHOOSE v \in Values : TRUE}]]
        /\ success = [p \in Threads \cup {"r1", "e1", "d1", "l1"} |-> FALSE]
        /\ searchRet = [p \in Threads \cup {"r1", "e1", "d1", "l1"} |-> Bot]
        /\ heap =    [i \in 1..MaxHeap |->
                  IF i <= Cardinality(Components)
                  THEN [val |-> Bot, snapNum |-> 0, left |-> Null, right |-> Null]
                  ELSE [val |-> Bot, snapNum |-> -1, left |-> Null, right |-> Null]]
        /\ freePtr = Cardinality(Components) + 1
        /\ rootPtr = [c \in Components |-> CompIdx(c)]
        (* Procedure CatchUpTreeProc *)
        /\ comp_ = [ self \in ProcSet |-> defaultInitValue]
        /\ k = [ self \in ProcSet |-> 1]
        /\ lastPtr = [ self \in ProcSet |-> Null]
        /\ cnt = [ self \in ProcSet |-> 0]
        /\ liveVal = [ self \in ProcSet |-> Bot]
        /\ targetIdx = [ self \in ProcSet |-> 0]
        /\ newNode = [ self \in ProcSet |-> Null]
        /\ parentIdx = [ self \in ProcSet |-> 0]
        /\ path_ = [ self \in ProcSet |-> <<>>]
        /\ curr_ = [ self \in ProcSet |-> Null]
        /\ loopStep_ = [ self \in ProcSet |-> 1]
        (* Procedure SearchTreeProc *)
        /\ comp = [ self \in ProcSet |-> defaultInitValue]
        /\ targetSnap = [ self \in ProcSet |-> defaultInitValue]
        /\ low = [ self \in ProcSet |-> 2]
        /\ high = [ self \in ProcSet |-> 0]
        /\ mid = [ self \in ProcSet |-> 0]
        /\ midPtr = [ self \in ProcSet |-> Null]
        /\ closestMatchVal = [ self \in ProcSet |-> Bot]
        /\ path = [ self \in ProcSet |-> <<>>]
        /\ curr = [ self \in ProcSet |-> Null]
        /\ loopStep = [ self \in ProcSet |-> 1]
        (* Process Client *)
        /\ targetComp = [self \in Threads |-> CHOOSE c \in Components : TRUE]
        /\ newVal = [self \in Threads |-> CHOOSE v \in Values : TRUE]
        /\ ops = [self \in Threads |-> 0]
        (* Process Reader *)
        /\ searchComp = CHOOSE c \in Components : TRUE
        /\ targetSnapshot \in {0, MaxClock}
        /\ finalResult = Bot
        (* Process Exporter *)
        /\ expComp = CHOOSE c \in Components : TRUE
        /\ snapBoundary = 0
        /\ exportLimit = 0
        /\ bfsQueue = <<>>
        /\ visitedCount = 0
        /\ currExportPtr = Null
        /\ exportedSnaps = <<>>
        /\ exportedVals = <<>>
        (* Process Deleter *)
        /\ delComp = CHOOSE c \in Components : TRUE
        (* Process LiveReader *)
        /\ liveComp = CHOOSE c \in Components : TRUE
        /\ liveResult = Bot
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Threads -> "ClientLoop"
                                        [] self = "r1" -> "Reader_Start"
                                        [] self = "e1" -> "Export_Start"
                                        [] self = "d1" -> "Delete_Await"
                                        [] self = "l1" -> "Check_Alive"]

CatchUp_Check(self) == /\ pc[self] = "CatchUp_Check"
                       /\ IF c_deleted[comp_[self]] = TRUE
                             THEN /\ success' = [success EXCEPT ![self] = TRUE]
                                  /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                                  /\ UNCHANGED << k, lastPtr >>
                             ELSE /\ k' = [k EXCEPT ![self] = c_nodeCount[comp_[self]]]
                                  /\ lastPtr' = [lastPtr EXCEPT ![self] = GetPhysicalNode(comp_[self], k'[self])]
                                  /\ IF lastPtr'[self] /= Null /\ COUNT <= heap[lastPtr'[self]].snapNum
                                        THEN /\ success' = [success EXCEPT ![self] = TRUE]
                                             /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "CatchUp_SetTarget"]
                                             /\ UNCHANGED success
                       /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                       history, searchRet, heap, freePtr, 
                                       rootPtr, stack, comp_, cnt, liveVal, 
                                       targetIdx, newNode, parentIdx, path_, 
                                       curr_, loopStep_, comp, targetSnap, low, 
                                       high, mid, midPtr, closestMatchVal, 
                                       path, curr, loopStep, targetComp, 
                                       newVal, ops, searchComp, targetSnapshot, 
                                       finalResult, expComp, snapBoundary, 
                                       exportLimit, bfsQueue, visitedCount, 
                                       currExportPtr, exportedSnaps, 
                                       exportedVals, delComp, liveComp, 
                                       liveResult >>

CatchUp_SetTarget(self) == /\ pc[self] = "CatchUp_SetTarget"
                           /\ liveVal' = [liveVal EXCEPT ![self] = c_val[comp_[self]]]
                           /\ cnt' = [cnt EXCEPT ![self] = COUNT]
                           /\ targetIdx' = [targetIdx EXCEPT ![self] = k[self] + 1]
                           /\ IF targetIdx'[self] > MaxNodes \/ freePtr > MaxHeap
                                 THEN /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                                      /\ UNCHANGED << success, parentIdx, 
                                                      path_, curr_, loopStep_ >>
                                 ELSE /\ IF cnt'[self] <= heap[lastPtr[self]].snapNum
                                            THEN /\ success' = [success EXCEPT ![self] = TRUE]
                                                 /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                                                 /\ UNCHANGED << parentIdx, 
                                                                 path_, curr_, 
                                                                 loopStep_ >>
                                            ELSE /\ parentIdx' = [parentIdx EXCEPT ![self] = targetIdx'[self] \div 2]
                                                 /\ path_' = [path_ EXCEPT ![self] = GetPath(parentIdx'[self])]
                                                 /\ curr_' = [curr_ EXCEPT ![self] = rootPtr[comp_[self]]]
                                                 /\ loopStep_' = [loopStep_ EXCEPT ![self] = 1]
                                                 /\ pc' = [pc EXCEPT ![self] = "CatchUp_GetNode_Loop"]
                                                 /\ UNCHANGED success
                           /\ UNCHANGED << COUNT, c_val, c_nodeCount, 
                                           c_deleted, history, searchRet, heap, 
                                           freePtr, rootPtr, stack, comp_, k, 
                                           lastPtr, newNode, comp, targetSnap, 
                                           low, high, mid, midPtr, 
                                           closestMatchVal, path, curr, 
                                           loopStep, targetComp, newVal, ops, 
                                           searchComp, targetSnapshot, 
                                           finalResult, expComp, snapBoundary, 
                                           exportLimit, bfsQueue, visitedCount, 
                                           currExportPtr, exportedSnaps, 
                                           exportedVals, delComp, liveComp, 
                                           liveResult >>

CatchUp_GetNode_Loop(self) == /\ pc[self] = "CatchUp_GetNode_Loop"
                              /\ IF loopStep_[self] <= Len(path_[self]) /\ curr_[self] /= Null
                                    THEN /\ IF path_[self][loopStep_[self]] = "L"
                                               THEN /\ curr_' = [curr_ EXCEPT ![self] = heap[curr_[self]].left]
                                               ELSE /\ curr_' = [curr_ EXCEPT ![self] = heap[curr_[self]].right]
                                         /\ loopStep_' = [loopStep_ EXCEPT ![self] = loopStep_[self] + 1]
                                         /\ pc' = [pc EXCEPT ![self] = "CatchUp_GetNode_Loop"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "CatchUp_Alloc"]
                                         /\ UNCHANGED << curr_, loopStep_ >>
                              /\ UNCHANGED << COUNT, c_val, c_nodeCount, 
                                              c_deleted, history, success, 
                                              searchRet, heap, freePtr, 
                                              rootPtr, stack, comp_, k, 
                                              lastPtr, cnt, liveVal, targetIdx, 
                                              newNode, parentIdx, path_, comp, 
                                              targetSnap, low, high, mid, 
                                              midPtr, closestMatchVal, path, 
                                              curr, loopStep, targetComp, 
                                              newVal, ops, searchComp, 
                                              targetSnapshot, finalResult, 
                                              expComp, snapBoundary, 
                                              exportLimit, bfsQueue, 
                                              visitedCount, currExportPtr, 
                                              exportedSnaps, exportedVals, 
                                              delComp, liveComp, liveResult >>

CatchUp_Alloc(self) == /\ pc[self] = "CatchUp_Alloc"
                       /\ IF curr_[self] = Null
                             THEN /\ success' = FALSE
                                  /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                                  /\ UNCHANGED << c_nodeCount, heap, freePtr, 
                                                  newNode >>
                             ELSE /\ IF (targetIdx[self] % 2 = 0 /\ heap[curr_[self]].left /= Null) \/ (targetIdx[self] % 2 /= 0 /\ heap[curr_[self]].right /= Null)
                                        THEN /\ IF c_nodeCount[comp_[self]] = k[self]
                                                   THEN /\ c_nodeCount' = [c_nodeCount EXCEPT ![comp_[self]] = targetIdx[self]]
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED c_nodeCount
                                             /\ pc' = [pc EXCEPT ![self] = "CatchUp_Check"]
                                             /\ UNCHANGED << success, heap, 
                                                             freePtr, newNode >>
                                        ELSE /\ IF liveVal[self] /= c_val[comp_[self]]
                                                   THEN /\ pc' = [pc EXCEPT ![self] = "CatchUp_Check"]
                                                        /\ UNCHANGED << success, 
                                                                        heap, 
                                                                        freePtr, 
                                                                        newNode >>
                                                   ELSE /\ IF freePtr > MaxHeap
                                                              THEN /\ success' = FALSE
                                                                   /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                                                                   /\ UNCHANGED << heap, 
                                                                                   freePtr, 
                                                                                   newNode >>
                                                              ELSE /\ newNode' = [newNode EXCEPT ![self] = freePtr]
                                                                   /\ freePtr' = freePtr + 1
                                                                   /\ heap' = [heap EXCEPT ![newNode'[self]] = [val |-> liveVal[self], snapNum |-> cnt[self], left |-> Null, right |-> Null]]
                                                                   /\ pc' = [pc EXCEPT ![self] = "CatchUp_CAS"]
                                                                   /\ UNCHANGED success
                                             /\ UNCHANGED c_nodeCount
                       /\ UNCHANGED << COUNT, c_val, c_deleted, history, 
                                       searchRet, rootPtr, stack, comp_, k, 
                                       lastPtr, cnt, liveVal, targetIdx, 
                                       parentIdx, path_, curr_, loopStep_, 
                                       comp, targetSnap, low, high, mid, 
                                       midPtr, closestMatchVal, path, curr, 
                                       loopStep, targetComp, newVal, ops, 
                                       searchComp, targetSnapshot, finalResult, 
                                       expComp, snapBoundary, exportLimit, 
                                       bfsQueue, visitedCount, currExportPtr, 
                                       exportedSnaps, exportedVals, delComp, 
                                       liveComp, liveResult >>

CatchUp_CAS(self) == /\ pc[self] = "CatchUp_CAS"
                     /\ IF c_nodeCount[comp_[self]] = k[self] /\ cnt[self] > heap[lastPtr[self]].snapNum
                           THEN /\ IF targetIdx[self] % 2 = 0
                                      THEN /\ IF heap[curr_[self]].left = Null
                                                 THEN /\ heap' = [heap EXCEPT ![curr_[self]].left = newNode[self]]
                                                      /\ success' = [success EXCEPT ![self] = TRUE]
                                                 ELSE /\ success' = [success EXCEPT ![self] = FALSE]
                                                      /\ heap' = heap
                                      ELSE /\ IF heap[curr_[self]].right = Null
                                                 THEN /\ heap' = [heap EXCEPT ![curr_[self]].right = newNode[self]]
                                                      /\ success' = [success EXCEPT ![self] = TRUE]
                                                 ELSE /\ success' = [success EXCEPT ![self] = FALSE]
                                                      /\ heap' = heap
                           ELSE /\ success' = [success EXCEPT ![self] = FALSE]
                                /\ heap' = heap
                     /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                     /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                     history, searchRet, freePtr, rootPtr, 
                                     stack, comp_, k, lastPtr, cnt, liveVal, 
                                     targetIdx, newNode, parentIdx, path_, 
                                     curr_, loopStep_, comp, targetSnap, low, 
                                     high, mid, midPtr, closestMatchVal, path, 
                                     curr, loopStep, targetComp, newVal, ops, 
                                     searchComp, targetSnapshot, finalResult, 
                                     expComp, snapBoundary, exportLimit, 
                                     bfsQueue, visitedCount, currExportPtr, 
                                     exportedSnaps, exportedVals, delComp, 
                                     liveComp, liveResult >>

CatchUp_End(self) == /\ pc[self] = "CatchUp_End"
                     /\ IF curr_[self] /= Null
                           THEN /\ IF (targetIdx[self] % 2 = 0 /\ heap[curr_[self]].left /= Null) \/ (targetIdx[self] % 2 /= 0 /\ heap[curr_[self]].right /= Null)
                                      THEN /\ IF c_nodeCount[comp_[self]] = k[self]
                                                 THEN /\ c_nodeCount' = [c_nodeCount EXCEPT ![comp_[self]] = targetIdx[self]]
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED c_nodeCount
                                      ELSE /\ TRUE
                                           /\ UNCHANGED c_nodeCount
                           ELSE /\ TRUE
                                /\ UNCHANGED c_nodeCount
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ k' = [k EXCEPT ![self] = Head(stack[self]).k]
                     /\ lastPtr' = [lastPtr EXCEPT ![self] = Head(stack[self]).lastPtr]
                     /\ cnt' = [cnt EXCEPT ![self] = Head(stack[self]).cnt]
                     /\ liveVal' = [liveVal EXCEPT ![self] = Head(stack[self]).liveVal]
                     /\ targetIdx' = [targetIdx EXCEPT ![self] = Head(stack[self]).targetIdx]
                     /\ newNode' = [newNode EXCEPT ![self] = Head(stack[self]).newNode]
                     /\ parentIdx' = [parentIdx EXCEPT ![self] = Head(stack[self]).parentIdx]
                     /\ path_' = [path_ EXCEPT ![self] = Head(stack[self]).path_]
                     /\ curr_' = [curr_ EXCEPT ![self] = Head(stack[self]).curr_]
                     /\ loopStep_' = [loopStep_ EXCEPT ![self] = Head(stack[self]).loopStep_]
                     /\ comp_' = [comp_ EXCEPT ![self] = Head(stack[self]).comp_]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << COUNT, c_val, c_deleted, history, success, 
                                     searchRet, heap, freePtr, rootPtr, comp, 
                                     targetSnap, low, high, mid, midPtr, 
                                     closestMatchVal, path, curr, loopStep, 
                                     targetComp, newVal, ops, searchComp, 
                                     targetSnapshot, finalResult, expComp, 
                                     snapBoundary, exportLimit, bfsQueue, 
                                     visitedCount, currExportPtr, 
                                     exportedSnaps, exportedVals, delComp, 
                                     liveComp, liveResult >>

CatchUpTreeProc(self) == CatchUp_Check(self) \/ CatchUp_SetTarget(self)
                            \/ CatchUp_GetNode_Loop(self)
                            \/ CatchUp_Alloc(self) \/ CatchUp_CAS(self)
                            \/ CatchUp_End(self)

Search_Init(self) == /\ pc[self] = "Search_Init"
                     /\ IF c_deleted[comp[self]] = TRUE
                           THEN /\ searchRet' = [searchRet EXCEPT ![self] = -99]
                                /\ pc' = [pc EXCEPT ![self] = "Search_End"]
                                /\ UNCHANGED << low, high, closestMatchVal >>
                           ELSE /\ IF targetSnap[self] <= heap[rootPtr[comp[self]]].snapNum
                                      THEN /\ searchRet' = [searchRet EXCEPT ![self] = Bot]
                                           /\ pc' = [pc EXCEPT ![self] = "Search_End"]
                                           /\ UNCHANGED << low, high, 
                                                           closestMatchVal >>
                                      ELSE /\ IF GetPhysicalNode(comp[self], c_nodeCount[comp[self]] + 1) /= Null
                                                 THEN /\ high' = [high EXCEPT ![self] = c_nodeCount[comp[self]] + 1]
                                                 ELSE /\ high' = [high EXCEPT ![self] = c_nodeCount[comp[self]]]
                                           /\ low' = [low EXCEPT ![self] = 2]
                                           /\ closestMatchVal' = [closestMatchVal EXCEPT ![self] = c_val[comp[self]]]
                                           /\ searchRet' = [searchRet EXCEPT ![self] = c_val[comp[self]]]
                                           /\ pc' = [pc EXCEPT ![self] = "Search_Loop"]
                     /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                     history, success, heap, freePtr, rootPtr, 
                                     stack, comp_, k, lastPtr, cnt, liveVal, 
                                     targetIdx, newNode, parentIdx, path_, 
                                     curr_, loopStep_, comp, targetSnap, mid, 
                                     midPtr, path, curr, loopStep, targetComp, 
                                     newVal, ops, searchComp, targetSnapshot, 
                                     finalResult, expComp, snapBoundary, 
                                     exportLimit, bfsQueue, visitedCount, 
                                     currExportPtr, exportedSnaps, 
                                     exportedVals, delComp, liveComp, 
                                     liveResult >>

Search_Loop(self) == /\ pc[self] = "Search_Loop"
                     /\ IF low[self] <= high[self]
                           THEN /\ mid' = [mid EXCEPT ![self] = low[self] + ((high[self] - low[self]) \div 2)]
                                /\ path' = [path EXCEPT ![self] = GetPath(mid'[self])]
                                /\ curr' = [curr EXCEPT ![self] = rootPtr[comp[self]]]
                                /\ loopStep' = [loopStep EXCEPT ![self] = 1]
                                /\ pc' = [pc EXCEPT ![self] = "Search_Walk"]
                                /\ UNCHANGED searchRet
                           ELSE /\ searchRet' = [searchRet EXCEPT ![self] = closestMatchVal[self]]
                                /\ pc' = [pc EXCEPT ![self] = "Search_End"]
                                /\ UNCHANGED << mid, path, curr, loopStep >>
                     /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                     history, success, heap, freePtr, rootPtr, 
                                     stack, comp_, k, lastPtr, cnt, liveVal, 
                                     targetIdx, newNode, parentIdx, path_, 
                                     curr_, loopStep_, comp, targetSnap, low, 
                                     high, midPtr, closestMatchVal, targetComp, 
                                     newVal, ops, searchComp, targetSnapshot, 
                                     finalResult, expComp, snapBoundary, 
                                     exportLimit, bfsQueue, visitedCount, 
                                     currExportPtr, exportedSnaps, 
                                     exportedVals, delComp, liveComp, 
                                     liveResult >>

Search_Walk(self) == /\ pc[self] = "Search_Walk"
                     /\ IF loopStep[self] <= Len(path[self]) /\ curr[self] /= Null
                           THEN /\ IF path[self][loopStep[self]] = "L"
                                      THEN /\ curr' = [curr EXCEPT ![self] = heap[curr[self]].left]
                                      ELSE /\ curr' = [curr EXCEPT ![self] = heap[curr[self]].right]
                                /\ loopStep' = [loopStep EXCEPT ![self] = loopStep[self] + 1]
                                /\ pc' = [pc EXCEPT ![self] = "Search_Walk"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "Search_Eval"]
                                /\ UNCHANGED << curr, loopStep >>
                     /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                     history, success, searchRet, heap, 
                                     freePtr, rootPtr, stack, comp_, k, 
                                     lastPtr, cnt, liveVal, targetIdx, newNode, 
                                     parentIdx, path_, curr_, loopStep_, comp, 
                                     targetSnap, low, high, mid, midPtr, 
                                     closestMatchVal, path, targetComp, newVal, 
                                     ops, searchComp, targetSnapshot, 
                                     finalResult, expComp, snapBoundary, 
                                     exportLimit, bfsQueue, visitedCount, 
                                     currExportPtr, exportedSnaps, 
                                     exportedVals, delComp, liveComp, 
                                     liveResult >>

Search_Eval(self) == /\ pc[self] = "Search_Eval"
                     /\ midPtr' = [midPtr EXCEPT ![self] = curr[self]]
                     /\ IF midPtr'[self] = Null
                           THEN /\ high' = [high EXCEPT ![self] = mid[self] - 1]
                                /\ UNCHANGED << low, closestMatchVal >>
                           ELSE /\ IF heap[midPtr'[self]].snapNum >= targetSnap[self]
                                      THEN /\ closestMatchVal' = [closestMatchVal EXCEPT ![self] = heap[midPtr'[self]].val]
                                           /\ high' = [high EXCEPT ![self] = mid[self] - 1]
                                           /\ low' = low
                                      ELSE /\ low' = [low EXCEPT ![self] = mid[self] + 1]
                                           /\ UNCHANGED << high, 
                                                           closestMatchVal >>
                     /\ pc' = [pc EXCEPT ![self] = "Search_Loop"]
                     /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                     history, success, searchRet, heap, 
                                     freePtr, rootPtr, stack, comp_, k, 
                                     lastPtr, cnt, liveVal, targetIdx, newNode, 
                                     parentIdx, path_, curr_, loopStep_, comp, 
                                     targetSnap, mid, path, curr, loopStep, 
                                     targetComp, newVal, ops, searchComp, 
                                     targetSnapshot, finalResult, expComp, 
                                     snapBoundary, exportLimit, bfsQueue, 
                                     visitedCount, currExportPtr, 
                                     exportedSnaps, exportedVals, delComp, 
                                     liveComp, liveResult >>

Search_End(self) == /\ pc[self] = "Search_End"
                    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                    /\ low' = [low EXCEPT ![self] = Head(stack[self]).low]
                    /\ high' = [high EXCEPT ![self] = Head(stack[self]).high]
                    /\ mid' = [mid EXCEPT ![self] = Head(stack[self]).mid]
                    /\ midPtr' = [midPtr EXCEPT ![self] = Head(stack[self]).midPtr]
                    /\ closestMatchVal' = [closestMatchVal EXCEPT ![self] = Head(stack[self]).closestMatchVal]
                    /\ path' = [path EXCEPT ![self] = Head(stack[self]).path]
                    /\ curr' = [curr EXCEPT ![self] = Head(stack[self]).curr]
                    /\ loopStep' = [loopStep EXCEPT ![self] = Head(stack[self]).loopStep]
                    /\ comp' = [comp EXCEPT ![self] = Head(stack[self]).comp]
                    /\ targetSnap' = [targetSnap EXCEPT ![self] = Head(stack[self]).targetSnap]
                    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                    history, success, searchRet, heap, freePtr, 
                                    rootPtr, comp_, k, lastPtr, cnt, liveVal, 
                                    targetIdx, newNode, parentIdx, path_, 
                                    curr_, loopStep_, targetComp, newVal, ops, 
                                    searchComp, targetSnapshot, finalResult, 
                                    expComp, snapBoundary, exportLimit, 
                                    bfsQueue, visitedCount, currExportPtr, 
                                    exportedSnaps, exportedVals, delComp, 
                                    liveComp, liveResult >>

SearchTreeProc(self) == Search_Init(self) \/ Search_Loop(self)
                           \/ Search_Walk(self) \/ Search_Eval(self)
                           \/ Search_End(self)

ClientLoop(self) == /\ pc[self] = "ClientLoop"
                    /\ IF ops[self] < 3
                          THEN /\ ops' = [ops EXCEPT ![self] = ops[self] + 1]
                               /\ \/ /\ pc' = [pc EXCEPT ![self] = "ClickOp"]
                                  \/ /\ pc' = [pc EXCEPT ![self] = "Update_Select"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ ops' = ops
                    /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                    history, success, searchRet, heap, freePtr, 
                                    rootPtr, stack, comp_, k, lastPtr, cnt, 
                                    liveVal, targetIdx, newNode, parentIdx, 
                                    path_, curr_, loopStep_, comp, targetSnap, 
                                    low, high, mid, midPtr, closestMatchVal, 
                                    path, curr, loopStep, targetComp, newVal, 
                                    searchComp, targetSnapshot, finalResult, 
                                    expComp, snapBoundary, exportLimit, 
                                    bfsQueue, visitedCount, currExportPtr, 
                                    exportedSnaps, exportedVals, delComp, 
                                    liveComp, liveResult >>

ClickOp(self) == /\ pc[self] = "ClickOp"
                 /\ IF COUNT < MaxClock
                       THEN /\ COUNT' = COUNT + 1
                            /\ history' = [c \in Components |-> [history[c] EXCEPT ![COUNT'] = {c_val[c]}]]
                       ELSE /\ TRUE
                            /\ UNCHANGED << COUNT, history >>
                 /\ pc' = [pc EXCEPT ![self] = "ClientLoop"]
                 /\ UNCHANGED << c_val, c_nodeCount, c_deleted, success, 
                                 searchRet, heap, freePtr, rootPtr, stack, 
                                 comp_, k, lastPtr, cnt, liveVal, targetIdx, 
                                 newNode, parentIdx, path_, curr_, loopStep_, 
                                 comp, targetSnap, low, high, mid, midPtr, 
                                 closestMatchVal, path, curr, loopStep, 
                                 targetComp, newVal, ops, searchComp, 
                                 targetSnapshot, finalResult, expComp, 
                                 snapBoundary, exportLimit, bfsQueue, 
                                 visitedCount, currExportPtr, exportedSnaps, 
                                 exportedVals, delComp, liveComp, liveResult >>

Update_Select(self) == /\ pc[self] = "Update_Select"
                       /\ \E c \in Components:
                            /\ targetComp' = [targetComp EXCEPT ![self] = c]
                            /\ newVal' = [newVal EXCEPT ![self] = IF ops[self] = 2 THEN (CHOOSE v \in Values : TRUE)
                                                                  ELSE (CHOOSE v \in Values : v /= (CHOOSE v2 \in Values : TRUE) \/ Cardinality(Values) = 1)]
                       /\ pc' = [pc EXCEPT ![self] = "Update_Catchup"]
                       /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                       history, success, searchRet, heap, 
                                       freePtr, rootPtr, stack, comp_, k, 
                                       lastPtr, cnt, liveVal, targetIdx, 
                                       newNode, parentIdx, path_, curr_, 
                                       loopStep_, comp, targetSnap, low, high, 
                                       mid, midPtr, closestMatchVal, path, 
                                       curr, loopStep, ops, searchComp, 
                                       targetSnapshot, finalResult, expComp, 
                                       snapBoundary, exportLimit, bfsQueue, 
                                       visitedCount, currExportPtr, 
                                       exportedSnaps, exportedVals, delComp, 
                                       liveComp, liveResult >>

Update_Catchup(self) == /\ pc[self] = "Update_Catchup"
                        /\ /\ comp_' = [comp_ EXCEPT ![self] = targetComp[self]]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CatchUpTreeProc",
                                                                    pc        |->  "Update_RetryCatchup",
                                                                    k         |->  k[self],
                                                                    lastPtr   |->  lastPtr[self],
                                                                    cnt       |->  cnt[self],
                                                                    liveVal   |->  liveVal[self],
                                                                    targetIdx |->  targetIdx[self],
                                                                    newNode   |->  newNode[self],
                                                                    parentIdx |->  parentIdx[self],
                                                                    path_     |->  path_[self],
                                                                    curr_     |->  curr_[self],
                                                                    loopStep_ |->  loopStep_[self],
                                                                    comp_     |->  comp_[self] ] >>
                                                                \o stack[self]]
                        /\ k' = [k EXCEPT ![self] = 1]
                        /\ lastPtr' = [lastPtr EXCEPT ![self] = Null]
                        /\ cnt' = [cnt EXCEPT ![self] = 0]
                        /\ liveVal' = [liveVal EXCEPT ![self] = Bot]
                        /\ targetIdx' = [targetIdx EXCEPT ![self] = 0]
                        /\ newNode' = [newNode EXCEPT ![self] = Null]
                        /\ parentIdx' = [parentIdx EXCEPT ![self] = 0]
                        /\ path_' = [path_ EXCEPT ![self] = <<>>]
                        /\ curr_' = [curr_ EXCEPT ![self] = Null]
                        /\ loopStep_' = [loopStep_ EXCEPT ![self] = 1]
                        /\ pc' = [pc EXCEPT ![self] = "CatchUp_Check"]
                        /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                        history, success, searchRet, heap, 
                                        freePtr, rootPtr, comp, targetSnap, 
                                        low, high, mid, midPtr, 
                                        closestMatchVal, path, curr, loopStep, 
                                        targetComp, newVal, ops, searchComp, 
                                        targetSnapshot, finalResult, expComp, 
                                        snapBoundary, exportLimit, bfsQueue, 
                                        visitedCount, currExportPtr, 
                                        exportedSnaps, exportedVals, delComp, 
                                        liveComp, liveResult >>

Update_RetryCatchup(self) == /\ pc[self] = "Update_RetryCatchup"
                             /\ IF ~success[self]
                                   THEN /\ /\ comp_' = [comp_ EXCEPT ![self] = targetComp[self]]
                                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CatchUpTreeProc",
                                                                                    pc        |->  "Update_Apply",
                                                                                    k         |->  k[self],
                                                                                    lastPtr   |->  lastPtr[self],
                                                                                    cnt       |->  cnt[self],
                                                                                    liveVal   |->  liveVal[self],
                                                                                    targetIdx |->  targetIdx[self],
                                                                                    newNode   |->  newNode[self],
                                                                                    parentIdx |->  parentIdx[self],
                                                                                    path_     |->  path_[self],
                                                                                    curr_     |->  curr_[self],
                                                                                    loopStep_ |->  loopStep_[self],
                                                                                    comp_     |->  comp_[self] ] >>
                                                                                \o stack[self]]
                                        /\ k' = [k EXCEPT ![self] = 1]
                                        /\ lastPtr' = [lastPtr EXCEPT ![self] = Null]
                                        /\ cnt' = [cnt EXCEPT ![self] = 0]
                                        /\ liveVal' = [liveVal EXCEPT ![self] = Bot]
                                        /\ targetIdx' = [targetIdx EXCEPT ![self] = 0]
                                        /\ newNode' = [newNode EXCEPT ![self] = Null]
                                        /\ parentIdx' = [parentIdx EXCEPT ![self] = 0]
                                        /\ path_' = [path_ EXCEPT ![self] = <<>>]
                                        /\ curr_' = [curr_ EXCEPT ![self] = Null]
                                        /\ loopStep_' = [loopStep_ EXCEPT ![self] = 1]
                                        /\ pc' = [pc EXCEPT ![self] = "CatchUp_Check"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "Update_Apply"]
                                        /\ UNCHANGED << stack, comp_, k, 
                                                        lastPtr, cnt, liveVal, 
                                                        targetIdx, newNode, 
                                                        parentIdx, path_, 
                                                        curr_, loopStep_ >>
                             /\ UNCHANGED << COUNT, c_val, c_nodeCount, 
                                             c_deleted, history, success, 
                                             searchRet, heap, freePtr, rootPtr, 
                                             comp, targetSnap, low, high, mid, 
                                             midPtr, closestMatchVal, path, 
                                             curr, loopStep, targetComp, 
                                             newVal, ops, searchComp, 
                                             targetSnapshot, finalResult, 
                                             expComp, snapBoundary, 
                                             exportLimit, bfsQueue, 
                                             visitedCount, currExportPtr, 
                                             exportedSnaps, exportedVals, 
                                             delComp, liveComp, liveResult >>

Update_Apply(self) == /\ pc[self] = "Update_Apply"
                      /\ IF c_deleted[targetComp[self]] = FALSE
                            THEN /\ c_val' = [c_val EXCEPT ![targetComp[self]] = newVal[self]]
                                 /\ history' = [history EXCEPT ![targetComp[self]][COUNT] = history[targetComp[self]][COUNT] \cup {newVal[self]}]
                            ELSE /\ TRUE
                                 /\ UNCHANGED << c_val, history >>
                      /\ pc' = [pc EXCEPT ![self] = "ClientLoop"]
                      /\ UNCHANGED << COUNT, c_nodeCount, c_deleted, success, 
                                      searchRet, heap, freePtr, rootPtr, stack, 
                                      comp_, k, lastPtr, cnt, liveVal, 
                                      targetIdx, newNode, parentIdx, path_, 
                                      curr_, loopStep_, comp, targetSnap, low, 
                                      high, mid, midPtr, closestMatchVal, path, 
                                      curr, loopStep, targetComp, newVal, ops, 
                                      searchComp, targetSnapshot, finalResult, 
                                      expComp, snapBoundary, exportLimit, 
                                      bfsQueue, visitedCount, currExportPtr, 
                                      exportedSnaps, exportedVals, delComp, 
                                      liveComp, liveResult >>

Client(self) == ClientLoop(self) \/ ClickOp(self) \/ Update_Select(self)
                   \/ Update_Catchup(self) \/ Update_RetryCatchup(self)
                   \/ Update_Apply(self)

Reader_Start == /\ pc["r1"] = "Reader_Start"
                /\ COUNT >= 2 \/ (\A t \in Threads : pc[t] = "Done")
                /\ IF targetSnapshot > heap[GetPhysicalNode(searchComp, c_nodeCount[searchComp])].snapNum
                      THEN /\ /\ comp_' = [comp_ EXCEPT !["r1"] = searchComp]
                              /\ stack' = [stack EXCEPT !["r1"] = << [ procedure |->  "CatchUpTreeProc",
                                                                       pc        |->  "Reader_RetryHelp",
                                                                       k         |->  k["r1"],
                                                                       lastPtr   |->  lastPtr["r1"],
                                                                       cnt       |->  cnt["r1"],
                                                                       liveVal   |->  liveVal["r1"],
                                                                       targetIdx |->  targetIdx["r1"],
                                                                       newNode   |->  newNode["r1"],
                                                                       parentIdx |->  parentIdx["r1"],
                                                                       path_     |->  path_["r1"],
                                                                       curr_     |->  curr_["r1"],
                                                                       loopStep_ |->  loopStep_["r1"],
                                                                       comp_     |->  comp_["r1"] ] >>
                                                                   \o stack["r1"]]
                           /\ k' = [k EXCEPT !["r1"] = 1]
                           /\ lastPtr' = [lastPtr EXCEPT !["r1"] = Null]
                           /\ cnt' = [cnt EXCEPT !["r1"] = 0]
                           /\ liveVal' = [liveVal EXCEPT !["r1"] = Bot]
                           /\ targetIdx' = [targetIdx EXCEPT !["r1"] = 0]
                           /\ newNode' = [newNode EXCEPT !["r1"] = Null]
                           /\ parentIdx' = [parentIdx EXCEPT !["r1"] = 0]
                           /\ path_' = [path_ EXCEPT !["r1"] = <<>>]
                           /\ curr_' = [curr_ EXCEPT !["r1"] = Null]
                           /\ loopStep_' = [loopStep_ EXCEPT !["r1"] = 1]
                           /\ pc' = [pc EXCEPT !["r1"] = "CatchUp_Check"]
                      ELSE /\ pc' = [pc EXCEPT !["r1"] = "Reader_RetryHelp"]
                           /\ UNCHANGED << stack, comp_, k, lastPtr, cnt, 
                                           liveVal, targetIdx, newNode, 
                                           parentIdx, path_, curr_, loopStep_ >>
                /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, history, 
                                success, searchRet, heap, freePtr, rootPtr, 
                                comp, targetSnap, low, high, mid, midPtr, 
                                closestMatchVal, path, curr, loopStep, 
                                targetComp, newVal, ops, searchComp, 
                                targetSnapshot, finalResult, expComp, 
                                snapBoundary, exportLimit, bfsQueue, 
                                visitedCount, currExportPtr, exportedSnaps, 
                                exportedVals, delComp, liveComp, liveResult >>

Reader_RetryHelp == /\ pc["r1"] = "Reader_RetryHelp"
                    /\ IF targetSnapshot > heap[GetPhysicalNode(searchComp, c_nodeCount[searchComp])].snapNum
                          THEN /\ /\ comp_' = [comp_ EXCEPT !["r1"] = searchComp]
                                  /\ stack' = [stack EXCEPT !["r1"] = << [ procedure |->  "CatchUpTreeProc",
                                                                           pc        |->  "Reader_InvokeSearch",
                                                                           k         |->  k["r1"],
                                                                           lastPtr   |->  lastPtr["r1"],
                                                                           cnt       |->  cnt["r1"],
                                                                           liveVal   |->  liveVal["r1"],
                                                                           targetIdx |->  targetIdx["r1"],
                                                                           newNode   |->  newNode["r1"],
                                                                           parentIdx |->  parentIdx["r1"],
                                                                           path_     |->  path_["r1"],
                                                                           curr_     |->  curr_["r1"],
                                                                           loopStep_ |->  loopStep_["r1"],
                                                                           comp_     |->  comp_["r1"] ] >>
                                                                       \o stack["r1"]]
                               /\ k' = [k EXCEPT !["r1"] = 1]
                               /\ lastPtr' = [lastPtr EXCEPT !["r1"] = Null]
                               /\ cnt' = [cnt EXCEPT !["r1"] = 0]
                               /\ liveVal' = [liveVal EXCEPT !["r1"] = Bot]
                               /\ targetIdx' = [targetIdx EXCEPT !["r1"] = 0]
                               /\ newNode' = [newNode EXCEPT !["r1"] = Null]
                               /\ parentIdx' = [parentIdx EXCEPT !["r1"] = 0]
                               /\ path_' = [path_ EXCEPT !["r1"] = <<>>]
                               /\ curr_' = [curr_ EXCEPT !["r1"] = Null]
                               /\ loopStep_' = [loopStep_ EXCEPT !["r1"] = 1]
                               /\ pc' = [pc EXCEPT !["r1"] = "CatchUp_Check"]
                          ELSE /\ pc' = [pc EXCEPT !["r1"] = "Reader_InvokeSearch"]
                               /\ UNCHANGED << stack, comp_, k, lastPtr, cnt, 
                                               liveVal, targetIdx, newNode, 
                                               parentIdx, path_, curr_, 
                                               loopStep_ >>
                    /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                    history, success, searchRet, heap, freePtr, 
                                    rootPtr, comp, targetSnap, low, high, mid, 
                                    midPtr, closestMatchVal, path, curr, 
                                    loopStep, targetComp, newVal, ops, 
                                    searchComp, targetSnapshot, finalResult, 
                                    expComp, snapBoundary, exportLimit, 
                                    bfsQueue, visitedCount, currExportPtr, 
                                    exportedSnaps, exportedVals, delComp, 
                                    liveComp, liveResult >>

Reader_InvokeSearch == /\ pc["r1"] = "Reader_InvokeSearch"
                       /\ /\ comp' = [comp EXCEPT !["r1"] = searchComp]
                          /\ stack' = [stack EXCEPT !["r1"] = << [ procedure |->  "SearchTreeProc",
                                                                   pc        |->  "Reader_Finish",
                                                                   low       |->  low["r1"],
                                                                   high      |->  high["r1"],
                                                                   mid       |->  mid["r1"],
                                                                   midPtr    |->  midPtr["r1"],
                                                                   closestMatchVal |->  closestMatchVal["r1"],
                                                                   path      |->  path["r1"],
                                                                   curr      |->  curr["r1"],
                                                                   loopStep  |->  loopStep["r1"],
                                                                   comp      |->  comp["r1"],
                                                                   targetSnap |->  targetSnap["r1"] ] >>
                                                               \o stack["r1"]]
                          /\ targetSnap' = [targetSnap EXCEPT !["r1"] = targetSnapshot]
                       /\ low' = [low EXCEPT !["r1"] = 2]
                       /\ high' = [high EXCEPT !["r1"] = 0]
                       /\ mid' = [mid EXCEPT !["r1"] = 0]
                       /\ midPtr' = [midPtr EXCEPT !["r1"] = Null]
                       /\ closestMatchVal' = [closestMatchVal EXCEPT !["r1"] = Bot]
                       /\ path' = [path EXCEPT !["r1"] = <<>>]
                       /\ curr' = [curr EXCEPT !["r1"] = Null]
                       /\ loopStep' = [loopStep EXCEPT !["r1"] = 1]
                       /\ pc' = [pc EXCEPT !["r1"] = "Search_Init"]
                       /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                       history, success, searchRet, heap, 
                                       freePtr, rootPtr, comp_, k, lastPtr, 
                                       cnt, liveVal, targetIdx, newNode, 
                                       parentIdx, path_, curr_, loopStep_, 
                                       targetComp, newVal, ops, searchComp, 
                                       targetSnapshot, finalResult, expComp, 
                                       snapBoundary, exportLimit, bfsQueue, 
                                       visitedCount, currExportPtr, 
                                       exportedSnaps, exportedVals, delComp, 
                                       liveComp, liveResult >>

Reader_Finish == /\ pc["r1"] = "Reader_Finish"
                 /\ finalResult' = searchRet["r1"]
                 /\ pc' = [pc EXCEPT !["r1"] = "Done"]
                 /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, history, 
                                 success, searchRet, heap, freePtr, rootPtr, 
                                 stack, comp_, k, lastPtr, cnt, liveVal, 
                                 targetIdx, newNode, parentIdx, path_, curr_, 
                                 loopStep_, comp, targetSnap, low, high, mid, 
                                 midPtr, closestMatchVal, path, curr, loopStep, 
                                 targetComp, newVal, ops, searchComp, 
                                 targetSnapshot, expComp, snapBoundary, 
                                 exportLimit, bfsQueue, visitedCount, 
                                 currExportPtr, exportedSnaps, exportedVals, 
                                 delComp, liveComp, liveResult >>

Reader == Reader_Start \/ Reader_RetryHelp \/ Reader_InvokeSearch
             \/ Reader_Finish

Export_Start == /\ pc["e1"] = "Export_Start"
                /\ pc["r1"]="Done"/\(\A t \in Threads : pc[t]="Done")
                /\ IF COUNT < MaxClock
                      THEN /\ COUNT' = COUNT + 1
                           /\ history' = [c \in Components |-> [history[c] EXCEPT ![COUNT'] = {c_val[c]}]]
                      ELSE /\ TRUE
                           /\ UNCHANGED << COUNT, history >>
                /\ snapBoundary' = COUNT'
                /\ IF c_deleted[expComp] = FALSE
                      THEN /\ /\ comp_' = [comp_ EXCEPT !["e1"] = expComp]
                              /\ stack' = [stack EXCEPT !["e1"] = << [ procedure |->  "CatchUpTreeProc",
                                                                       pc        |->  "Export_SecondCatchUp",
                                                                       k         |->  k["e1"],
                                                                       lastPtr   |->  lastPtr["e1"],
                                                                       cnt       |->  cnt["e1"],
                                                                       liveVal   |->  liveVal["e1"],
                                                                       targetIdx |->  targetIdx["e1"],
                                                                       newNode   |->  newNode["e1"],
                                                                       parentIdx |->  parentIdx["e1"],
                                                                       path_     |->  path_["e1"],
                                                                       curr_     |->  curr_["e1"],
                                                                       loopStep_ |->  loopStep_["e1"],
                                                                       comp_     |->  comp_["e1"] ] >>
                                                                   \o stack["e1"]]
                           /\ k' = [k EXCEPT !["e1"] = 1]
                           /\ lastPtr' = [lastPtr EXCEPT !["e1"] = Null]
                           /\ cnt' = [cnt EXCEPT !["e1"] = 0]
                           /\ liveVal' = [liveVal EXCEPT !["e1"] = Bot]
                           /\ targetIdx' = [targetIdx EXCEPT !["e1"] = 0]
                           /\ newNode' = [newNode EXCEPT !["e1"] = Null]
                           /\ parentIdx' = [parentIdx EXCEPT !["e1"] = 0]
                           /\ path_' = [path_ EXCEPT !["e1"] = <<>>]
                           /\ curr_' = [curr_ EXCEPT !["e1"] = Null]
                           /\ loopStep_' = [loopStep_ EXCEPT !["e1"] = 1]
                           /\ pc' = [pc EXCEPT !["e1"] = "CatchUp_Check"]
                      ELSE /\ pc' = [pc EXCEPT !["e1"] = "Export_SecondCatchUp"]
                           /\ UNCHANGED << stack, comp_, k, lastPtr, cnt, 
                                           liveVal, targetIdx, newNode, 
                                           parentIdx, path_, curr_, loopStep_ >>
                /\ UNCHANGED << c_val, c_nodeCount, c_deleted, success, 
                                searchRet, heap, freePtr, rootPtr, comp, 
                                targetSnap, low, high, mid, midPtr, 
                                closestMatchVal, path, curr, loopStep, 
                                targetComp, newVal, ops, searchComp, 
                                targetSnapshot, finalResult, expComp, 
                                exportLimit, bfsQueue, visitedCount, 
                                currExportPtr, exportedSnaps, exportedVals, 
                                delComp, liveComp, liveResult >>

Export_SecondCatchUp == /\ pc["e1"] = "Export_SecondCatchUp"
                        /\ IF c_deleted[expComp] = FALSE /\ ~success["e1"]
                              THEN /\ /\ comp_' = [comp_ EXCEPT !["e1"] = expComp]
                                      /\ stack' = [stack EXCEPT !["e1"] = << [ procedure |->  "CatchUpTreeProc",
                                                                               pc        |->  "Export_InitBFS",
                                                                               k         |->  k["e1"],
                                                                               lastPtr   |->  lastPtr["e1"],
                                                                               cnt       |->  cnt["e1"],
                                                                               liveVal   |->  liveVal["e1"],
                                                                               targetIdx |->  targetIdx["e1"],
                                                                               newNode   |->  newNode["e1"],
                                                                               parentIdx |->  parentIdx["e1"],
                                                                               path_     |->  path_["e1"],
                                                                               curr_     |->  curr_["e1"],
                                                                               loopStep_ |->  loopStep_["e1"],
                                                                               comp_     |->  comp_["e1"] ] >>
                                                                           \o stack["e1"]]
                                   /\ k' = [k EXCEPT !["e1"] = 1]
                                   /\ lastPtr' = [lastPtr EXCEPT !["e1"] = Null]
                                   /\ cnt' = [cnt EXCEPT !["e1"] = 0]
                                   /\ liveVal' = [liveVal EXCEPT !["e1"] = Bot]
                                   /\ targetIdx' = [targetIdx EXCEPT !["e1"] = 0]
                                   /\ newNode' = [newNode EXCEPT !["e1"] = Null]
                                   /\ parentIdx' = [parentIdx EXCEPT !["e1"] = 0]
                                   /\ path_' = [path_ EXCEPT !["e1"] = <<>>]
                                   /\ curr_' = [curr_ EXCEPT !["e1"] = Null]
                                   /\ loopStep_' = [loopStep_ EXCEPT !["e1"] = 1]
                                   /\ pc' = [pc EXCEPT !["e1"] = "CatchUp_Check"]
                              ELSE /\ pc' = [pc EXCEPT !["e1"] = "Export_InitBFS"]
                                   /\ UNCHANGED << stack, comp_, k, lastPtr, 
                                                   cnt, liveVal, targetIdx, 
                                                   newNode, parentIdx, path_, 
                                                   curr_, loopStep_ >>
                        /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                        history, success, searchRet, heap, 
                                        freePtr, rootPtr, comp, targetSnap, 
                                        low, high, mid, midPtr, 
                                        closestMatchVal, path, curr, loopStep, 
                                        targetComp, newVal, ops, searchComp, 
                                        targetSnapshot, finalResult, expComp, 
                                        snapBoundary, exportLimit, bfsQueue, 
                                        visitedCount, currExportPtr, 
                                        exportedSnaps, exportedVals, delComp, 
                                        liveComp, liveResult >>

Export_InitBFS == /\ pc["e1"] = "Export_InitBFS"
                  /\ IF c_deleted[expComp] = FALSE
                        THEN /\ exportLimit' = c_nodeCount[expComp]
                             /\ IF rootPtr[expComp] /= Null /\ exportLimit' >= 1
                                   THEN /\ bfsQueue' = <<rootPtr[expComp]>>
                                        /\ visitedCount' = 0
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << bfsQueue, visitedCount >>
                        ELSE /\ TRUE
                             /\ UNCHANGED << exportLimit, bfsQueue, 
                                             visitedCount >>
                  /\ pc' = [pc EXCEPT !["e1"] = "Export_BFSLoop"]
                  /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                  history, success, searchRet, heap, freePtr, 
                                  rootPtr, stack, comp_, k, lastPtr, cnt, 
                                  liveVal, targetIdx, newNode, parentIdx, 
                                  path_, curr_, loopStep_, comp, targetSnap, 
                                  low, high, mid, midPtr, closestMatchVal, 
                                  path, curr, loopStep, targetComp, newVal, 
                                  ops, searchComp, targetSnapshot, finalResult, 
                                  expComp, snapBoundary, currExportPtr, 
                                  exportedSnaps, exportedVals, delComp, 
                                  liveComp, liveResult >>

Export_BFSLoop == /\ pc["e1"] = "Export_BFSLoop"
                  /\ IF Len(bfsQueue) > 0 /\ visitedCount < exportLimit
                        THEN /\ currExportPtr' = Head(bfsQueue)
                             /\ visitedCount' = visitedCount + 1
                             /\ IF visitedCount' > 1
                                   THEN /\ exportedSnaps' = Append(exportedSnaps, heap[currExportPtr'].snapNum)
                                        /\ exportedVals' = Append(exportedVals, heap[currExportPtr'].val)
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << exportedSnaps, 
                                                        exportedVals >>
                             /\ bfsQueue' = Tail(bfsQueue)
                                            \o (IF heap[currExportPtr'].left /= Null THEN <<heap[currExportPtr'].left>> ELSE <<>>)
                                            \o (IF heap[currExportPtr'].right /= Null THEN <<heap[currExportPtr'].right>> ELSE <<>>)
                             /\ pc' = [pc EXCEPT !["e1"] = "Export_BFSLoop"]
                        ELSE /\ pc' = [pc EXCEPT !["e1"] = "Done"]
                             /\ UNCHANGED << bfsQueue, visitedCount, 
                                             currExportPtr, exportedSnaps, 
                                             exportedVals >>
                  /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                  history, success, searchRet, heap, freePtr, 
                                  rootPtr, stack, comp_, k, lastPtr, cnt, 
                                  liveVal, targetIdx, newNode, parentIdx, 
                                  path_, curr_, loopStep_, comp, targetSnap, 
                                  low, high, mid, midPtr, closestMatchVal, 
                                  path, curr, loopStep, targetComp, newVal, 
                                  ops, searchComp, targetSnapshot, finalResult, 
                                  expComp, snapBoundary, exportLimit, delComp, 
                                  liveComp, liveResult >>

Exporter == Export_Start \/ Export_SecondCatchUp \/ Export_InitBFS
               \/ Export_BFSLoop

Delete_Await == /\ pc["d1"] = "Delete_Await"
                /\ pc["e1"]="Done"
                /\ pc' = [pc EXCEPT !["d1"] = "Delete_Execute"]
                /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, history, 
                                success, searchRet, heap, freePtr, rootPtr, 
                                stack, comp_, k, lastPtr, cnt, liveVal, 
                                targetIdx, newNode, parentIdx, path_, curr_, 
                                loopStep_, comp, targetSnap, low, high, mid, 
                                midPtr, closestMatchVal, path, curr, loopStep, 
                                targetComp, newVal, ops, searchComp, 
                                targetSnapshot, finalResult, expComp, 
                                snapBoundary, exportLimit, bfsQueue, 
                                visitedCount, currExportPtr, exportedSnaps, 
                                exportedVals, delComp, liveComp, liveResult >>

Delete_Execute == /\ pc["d1"] = "Delete_Execute"
                  /\ c_deleted' = [c_deleted EXCEPT ![delComp] = TRUE]
                  /\ pc' = [pc EXCEPT !["d1"] = "Done"]
                  /\ UNCHANGED << COUNT, c_val, c_nodeCount, history, success, 
                                  searchRet, heap, freePtr, rootPtr, stack, 
                                  comp_, k, lastPtr, cnt, liveVal, targetIdx, 
                                  newNode, parentIdx, path_, curr_, loopStep_, 
                                  comp, targetSnap, low, high, mid, midPtr, 
                                  closestMatchVal, path, curr, loopStep, 
                                  targetComp, newVal, ops, searchComp, 
                                  targetSnapshot, finalResult, expComp, 
                                  snapBoundary, exportLimit, bfsQueue, 
                                  visitedCount, currExportPtr, exportedSnaps, 
                                  exportedVals, delComp, liveComp, liveResult >>

Deleter == Delete_Await \/ Delete_Execute

Check_Alive == /\ pc["l1"] = "Check_Alive"
               /\ pc["e1"]="Done"
               /\ IF c_deleted[liveComp] = TRUE
                     THEN /\ liveResult' = -99
                     ELSE /\ liveResult' = c_val[liveComp]
               /\ pc' = [pc EXCEPT !["l1"] = "Done"]
               /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, history, 
                               success, searchRet, heap, freePtr, rootPtr, 
                               stack, comp_, k, lastPtr, cnt, liveVal, 
                               targetIdx, newNode, parentIdx, path_, curr_, 
                               loopStep_, comp, targetSnap, low, high, mid, 
                               midPtr, closestMatchVal, path, curr, loopStep, 
                               targetComp, newVal, ops, searchComp, 
                               targetSnapshot, finalResult, expComp, 
                               snapBoundary, exportLimit, bfsQueue, 
                               visitedCount, currExportPtr, exportedSnaps, 
                               exportedVals, delComp, liveComp >>

LiveReader == Check_Alive

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Reader \/ Exporter \/ Deleter \/ LiveReader
           \/ (\E self \in ProcSet:  \/ CatchUpTreeProc(self)
                                     \/ SearchTreeProc(self))
           \/ (\E self \in Threads: Client(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* -------------------------------------------------------------------------
\* CUSTOM INVARIANTS FOR SEARCH, EXPORT & LINEARIZABILITY VERIFICATION
\* -------------------------------------------------------------------------
TypeOK ==
    /\ COUNT \in 0..MaxClock
    /\ c_val \in [Components -> Values \cup {Bot}]
    /\ c_nodeCount \in [Components -> 1..MaxNodes]
    /\ c_deleted \in [Components -> BOOLEAN]
    /\ freePtr \in 1..(MaxHeap + 1)
    /\ rootPtr \in [Components -> 1..MaxHeap \cup {Null}]

PointerIntegrityPhysical ==
    \A i \in 1..(freePtr - 1) :
        LET node == heap[i]
        IN /\ (node.left /= Null => node.left \in 1..(freePtr - 1))
           /\ (node.right /= Null => node.right \in 1..(freePtr - 1))

CompleteBinaryTreeTopologyPhysical == 
    \A c \in Components :
        c_deleted[c] = FALSE =>
            /\ \A i \in 1..c_nodeCount[c] : GetPhysicalNode(c, i) /= Null
            /\ \A i \in 2..c_nodeCount[c] : GetPhysicalNode(c, i \div 2) /= Null

MonotonicSnapshotsPhysical == 
    \A c \in Components :
        c_deleted[c] = FALSE =>
            /\ \A i \in 2..c_nodeCount[c] :
                LET currNode == GetPhysicalNode(c, i)
                    parentNode == GetPhysicalNode(c, i \div 2)
                IN (currNode /= Null) => 
                       /\ parentNode /= Null
                       /\ heap[currNode].snapNum > heap[parentNode].snapNum
            /\ \A i, j \in 1..c_nodeCount[c] :
                (i < j) => (heap[GetPhysicalNode(c, i)].snapNum < heap[GetPhysicalNode(c, j)].snapNum)

SnapshotValueConsistencyPhysical ==
    \A c \in Components :
        c_deleted[c] = FALSE =>
            \A i \in 2..c_nodeCount[c] :
                LET currNode == GetPhysicalNode(c, i)
                IN (currNode /= Null) =>
                   /\ heap[currNode].val \in Values
                   /\ heap[currNode].val \in history[c][heap[currNode].snapNum]

LiveReaderSafety ==
    (liveResult /= Bot) => (liveResult \in Values \cup {-99})

\* Verifies R2, R4 #4, R5: SearchTree returns a linearizable state from the sequential history
SearchLinearizable ==
    (pc["r1"] = "Done") =>
        \/ finalResult = -99
        \/ (targetSnapshot = 0 /\ finalResult = Bot)
        \/ (targetSnapshot > 0 /\ finalResult \in Values /\
            (\E t \in 0..MaxClock : finalResult \in history[searchComp][t]))

\* Verifies R3 #2: Bounded-Prefix BFS Export (Algorithm 5) never reads gaps or out-of-order nodes
ExportPrefixSafety ==
    /\ \A i \in 1..Len(exportedVals) : exportedVals[i] \in Values
    /\ \A i, j \in 1..Len(exportedSnaps) : (i < j) => (exportedSnaps[i] < exportedSnaps[j])

=============================================================================
