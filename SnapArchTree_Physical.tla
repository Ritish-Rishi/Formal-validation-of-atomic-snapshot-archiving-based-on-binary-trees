----------------------- MODULE SnapArchTree_Physical -----------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS Threads, Components, MaxClock, MaxNodes, Values, Bot, Null

\* Deterministic helper to assign initial root heap slots 1..Cardinality(Components)
CompIdx(c) == CHOOSE i \in 1..Cardinality(Components) :
    Cardinality({x \in Components : x <= c}) = i

MaxHeap == Cardinality(Components) * (MaxNodes + 4 * Cardinality(Threads) + 6)

\* -------------------------------------------------------------------------
\* BITWISE PATHFINDING SIMULATOR (Does not depend on state variables)
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
    
    \* Sequential ground-truth history log: history[c][t] stores valid states at snapshot t
    history = [c \in Components |-> [t \in 0..MaxClock |-> IF t = 0 THEN {Bot} ELSE {CHOOSE v \in Values : TRUE}]],
    
    \* THE PHYSICAL MEMORY POOL (Roots k=1 pre-allocated at 1..Cardinality(Components))
    heap = [i \in 1..MaxHeap |-> 
        IF i <= Cardinality(Components) 
        THEN [val |-> Bot, snapNum |-> 0, left |-> Null, right |-> Null]
        ELSE [val |-> Bot, snapNum |-> -1, left |-> Null, right |-> Null]],
    freePtr = Cardinality(Components) + 1,
    rootPtr = [c \in Components |-> CompIdx(c)];

define
    GetPhysicalNode(c, idx) == FindNodeH(heap, rootPtr[c], GetPath(idx), 1)
end define;

procedure CatchUpTreeProc(comp) 
variables 
    k = 1, lastPtr = Null, cnt = 0, liveVal = Bot, targetIdx = 0, 
    newNode = Null, parentIdx = 0, path = <<>>, curr = Null, loopStep = 1;
begin
CatchUp_Check:
    if c_deleted[comp] = TRUE then
        success := TRUE;
        goto CatchUp_End;
    else
        k := c_nodeCount[comp];
        lastPtr := GetPhysicalNode(comp, k);
        if lastPtr /= Null /\ COUNT <= heap[lastPtr].snapNum then
            success := TRUE;
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
        success := TRUE;
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
    elsif liveVal /= c_val[comp] then
        goto CatchUp_Check;
    elsif freePtr > MaxHeap then
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
                success := TRUE;
            else
                success := FALSE;
            end if;
        else
            if heap[curr].right = Null then
                heap[curr].right := newNode;
                success := TRUE;
            else
                success := FALSE;
            end if;
        end if;
    else
        success := FALSE;
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

process Client \in Threads
variables 
    targetComp \in Components, 
    newVal \in Values, 
    success = FALSE,
    ops = 0;
begin
ClientLoop:
    while ops < 3 do
        ops := ops + 1;
        
        either
            ClickOp:
                if COUNT < MaxClock then 
                    COUNT := COUNT + 1;
                    \* Seal ground-truth snapshot state at epoch COUNT for all components
                    history := [c \in Components |-> [history[c] EXCEPT ![COUNT] = {c_val[c]}]];
                end if;
        or
            Update_Select:
                with c \in Components, v \in Values do
                    targetComp := c;
                    newVal := v;
                end with;
            Update_Catchup:
                call CatchUpTreeProc(targetComp);
            Update_RetryCatchup:
                if ~success then
                    call CatchUpTreeProc(targetComp);
                end if;
            Update_Apply:
                c_val[targetComp] := newVal;
                if COUNT > 0 then
                    history[targetComp][COUNT] := history[targetComp][COUNT] \cup {newVal};
                end if;
        end either;
    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8b573ff6" /\ chksum(tla) = "a5116259")
CONSTANT defaultInitValue
VARIABLES COUNT, c_val, c_nodeCount, c_deleted, history, heap, freePtr, 
          rootPtr, pc, stack

(* define statement *)
GetPhysicalNode(c, idx) == FindNodeH(heap, rootPtr[c], GetPath(idx), 1)

VARIABLES comp, k, lastPtr, cnt, liveVal, targetIdx, newNode, parentIdx, path, 
          curr, loopStep, targetComp, newVal, success, ops

vars == << COUNT, c_val, c_nodeCount, c_deleted, history, heap, freePtr, 
           rootPtr, pc, stack, comp, k, lastPtr, cnt, liveVal, targetIdx, 
           newNode, parentIdx, path, curr, loopStep, targetComp, newVal, 
           success, ops >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ COUNT = 0
        /\ c_val = [c \in Components |-> CHOOSE v \in Values : TRUE]
        /\ c_nodeCount = [c \in Components |-> 1]
        /\ c_deleted = [c \in Components |-> FALSE]
        /\ history = [c \in Components |-> [t \in 0..MaxClock |-> IF t = 0 THEN {Bot} ELSE {CHOOSE v \in Values : TRUE}]]
        /\ heap =    [i \in 1..MaxHeap |->
                  IF i <= Cardinality(Components)
                  THEN [val |-> Bot, snapNum |-> 0, left |-> Null, right |-> Null]
                  ELSE [val |-> Bot, snapNum |-> -1, left |-> Null, right |-> Null]]
        /\ freePtr = Cardinality(Components) + 1
        /\ rootPtr = [c \in Components |-> CompIdx(c)]
        (* Procedure CatchUpTreeProc *)
        /\ comp = [ self \in ProcSet |-> defaultInitValue]
        /\ k = [ self \in ProcSet |-> 1]
        /\ lastPtr = [ self \in ProcSet |-> Null]
        /\ cnt = [ self \in ProcSet |-> 0]
        /\ liveVal = [ self \in ProcSet |-> Bot]
        /\ targetIdx = [ self \in ProcSet |-> 0]
        /\ newNode = [ self \in ProcSet |-> Null]
        /\ parentIdx = [ self \in ProcSet |-> 0]
        /\ path = [ self \in ProcSet |-> <<>>]
        /\ curr = [ self \in ProcSet |-> Null]
        /\ loopStep = [ self \in ProcSet |-> 1]
        (* Process Client *)
        /\ targetComp \in [Threads -> Components]
        /\ newVal \in [Threads -> Values]
        /\ success = [self \in Threads |-> FALSE]
        /\ ops = [self \in Threads |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "ClientLoop"]

CatchUp_Check(self) == /\ pc[self] = "CatchUp_Check"
                       /\ IF c_deleted[comp[self]] = TRUE
                             THEN /\ success' = [success EXCEPT ![self] = TRUE]
                                  /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                                  /\ UNCHANGED << k, lastPtr >>
                             ELSE /\ k' = [k EXCEPT ![self] = c_nodeCount[comp[self]]]
                                  /\ lastPtr' = [lastPtr EXCEPT ![self] = GetPhysicalNode(comp[self], k'[self])]
                                  /\ IF lastPtr'[self] /= Null /\ COUNT <= heap[lastPtr'[self]].snapNum
                                        THEN /\ success' = [success EXCEPT ![self] = TRUE]
                                             /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                                        ELSE /\ pc' = [pc EXCEPT ![self] = "CatchUp_SetTarget"]
                                             /\ UNCHANGED success
                       /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                       history, heap, freePtr, rootPtr, stack, 
                                       comp, cnt, liveVal, targetIdx, newNode, 
                                       parentIdx, path, curr, loopStep, 
                                       targetComp, newVal, ops >>

CatchUp_SetTarget(self) == /\ pc[self] = "CatchUp_SetTarget"
                           /\ liveVal' = [liveVal EXCEPT ![self] = c_val[comp[self]]]
                           /\ cnt' = [cnt EXCEPT ![self] = COUNT]
                           /\ targetIdx' = [targetIdx EXCEPT ![self] = k[self] + 1]
                           /\ IF targetIdx'[self] > MaxNodes \/ freePtr > MaxHeap
                                 THEN /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                                      /\ UNCHANGED << parentIdx, path, curr, 
                                                      loopStep, success >>
                                 ELSE /\ IF cnt'[self] <= heap[lastPtr[self]].snapNum
                                            THEN /\ success' = [success EXCEPT ![self] = TRUE]
                                                 /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                                                 /\ UNCHANGED << parentIdx, 
                                                                 path, curr, 
                                                                 loopStep >>
                                            ELSE /\ parentIdx' = [parentIdx EXCEPT ![self] = targetIdx'[self] \div 2]
                                                 /\ path' = [path EXCEPT ![self] = GetPath(parentIdx'[self])]
                                                 /\ curr' = [curr EXCEPT ![self] = rootPtr[comp[self]]]
                                                 /\ loopStep' = [loopStep EXCEPT ![self] = 1]
                                                 /\ pc' = [pc EXCEPT ![self] = "CatchUp_GetNode_Loop"]
                                                 /\ UNCHANGED success
                           /\ UNCHANGED << COUNT, c_val, c_nodeCount, 
                                           c_deleted, history, heap, freePtr, 
                                           rootPtr, stack, comp, k, lastPtr, 
                                           newNode, targetComp, newVal, ops >>

CatchUp_GetNode_Loop(self) == /\ pc[self] = "CatchUp_GetNode_Loop"
                              /\ IF loopStep[self] <= Len(path[self]) /\ curr[self] /= Null
                                    THEN /\ IF path[self][loopStep[self]] = "L"
                                               THEN /\ curr' = [curr EXCEPT ![self] = heap[curr[self]].left]
                                               ELSE /\ curr' = [curr EXCEPT ![self] = heap[curr[self]].right]
                                         /\ loopStep' = [loopStep EXCEPT ![self] = loopStep[self] + 1]
                                         /\ pc' = [pc EXCEPT ![self] = "CatchUp_GetNode_Loop"]
                                    ELSE /\ pc' = [pc EXCEPT ![self] = "CatchUp_Alloc"]
                                         /\ UNCHANGED << curr, loopStep >>
                              /\ UNCHANGED << COUNT, c_val, c_nodeCount, 
                                              c_deleted, history, heap, 
                                              freePtr, rootPtr, stack, comp, k, 
                                              lastPtr, cnt, liveVal, targetIdx, 
                                              newNode, parentIdx, path, 
                                              targetComp, newVal, success, ops >>

CatchUp_Alloc(self) == /\ pc[self] = "CatchUp_Alloc"
                       /\ IF curr[self] = Null
                             THEN /\ success' = [success EXCEPT ![self] = FALSE]
                                  /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                                  /\ UNCHANGED << heap, freePtr, newNode >>
                             ELSE /\ IF liveVal[self] /= c_val[comp[self]]
                                        THEN /\ pc' = [pc EXCEPT ![self] = "CatchUp_Check"]
                                             /\ UNCHANGED << heap, freePtr, 
                                                             newNode, success >>
                                        ELSE /\ IF freePtr > MaxHeap
                                                   THEN /\ success' = [success EXCEPT ![self] = FALSE]
                                                        /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                                                        /\ UNCHANGED << heap, 
                                                                        freePtr, 
                                                                        newNode >>
                                                   ELSE /\ newNode' = [newNode EXCEPT ![self] = freePtr]
                                                        /\ freePtr' = freePtr + 1
                                                        /\ heap' = [heap EXCEPT ![newNode'[self]] = [val |-> liveVal[self], snapNum |-> cnt[self], left |-> Null, right |-> Null]]
                                                        /\ pc' = [pc EXCEPT ![self] = "CatchUp_CAS"]
                                                        /\ UNCHANGED success
                       /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                       history, rootPtr, stack, comp, k, 
                                       lastPtr, cnt, liveVal, targetIdx, 
                                       parentIdx, path, curr, loopStep, 
                                       targetComp, newVal, ops >>

CatchUp_CAS(self) == /\ pc[self] = "CatchUp_CAS"
                     /\ IF c_nodeCount[comp[self]] = k[self] /\ cnt[self] > heap[lastPtr[self]].snapNum
                           THEN /\ IF targetIdx[self] % 2 = 0
                                      THEN /\ IF heap[curr[self]].left = Null
                                                 THEN /\ heap' = [heap EXCEPT ![curr[self]].left = newNode[self]]
                                                      /\ success' = [success EXCEPT ![self] = TRUE]
                                                 ELSE /\ success' = [success EXCEPT ![self] = FALSE]
                                                      /\ heap' = heap
                                      ELSE /\ IF heap[curr[self]].right = Null
                                                 THEN /\ heap' = [heap EXCEPT ![curr[self]].right = newNode[self]]
                                                      /\ success' = [success EXCEPT ![self] = TRUE]
                                                 ELSE /\ success' = [success EXCEPT ![self] = FALSE]
                                                      /\ heap' = heap
                           ELSE /\ success' = [success EXCEPT ![self] = FALSE]
                                /\ heap' = heap
                     /\ pc' = [pc EXCEPT ![self] = "CatchUp_End"]
                     /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                     history, freePtr, rootPtr, stack, comp, k, 
                                     lastPtr, cnt, liveVal, targetIdx, newNode, 
                                     parentIdx, path, curr, loopStep, 
                                     targetComp, newVal, ops >>

CatchUp_End(self) == /\ pc[self] = "CatchUp_End"
                     /\ IF curr[self] /= Null
                           THEN /\ IF (targetIdx[self] % 2 = 0 /\ heap[curr[self]].left /= Null) \/ (targetIdx[self] % 2 /= 0 /\ heap[curr[self]].right /= Null)
                                      THEN /\ IF c_nodeCount[comp[self]] = k[self]
                                                 THEN /\ c_nodeCount' = [c_nodeCount EXCEPT ![comp[self]] = targetIdx[self]]
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
                     /\ path' = [path EXCEPT ![self] = Head(stack[self]).path]
                     /\ curr' = [curr EXCEPT ![self] = Head(stack[self]).curr]
                     /\ loopStep' = [loopStep EXCEPT ![self] = Head(stack[self]).loopStep]
                     /\ comp' = [comp EXCEPT ![self] = Head(stack[self]).comp]
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << COUNT, c_val, c_deleted, history, heap, 
                                     freePtr, rootPtr, targetComp, newVal, 
                                     success, ops >>

CatchUpTreeProc(self) == CatchUp_Check(self) \/ CatchUp_SetTarget(self)
                            \/ CatchUp_GetNode_Loop(self)
                            \/ CatchUp_Alloc(self) \/ CatchUp_CAS(self)
                            \/ CatchUp_End(self)

ClientLoop(self) == /\ pc[self] = "ClientLoop"
                    /\ IF ops[self] < 3
                          THEN /\ ops' = [ops EXCEPT ![self] = ops[self] + 1]
                               /\ \/ /\ pc' = [pc EXCEPT ![self] = "ClickOp"]
                                  \/ /\ pc' = [pc EXCEPT ![self] = "Update_Select"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                               /\ ops' = ops
                    /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                    history, heap, freePtr, rootPtr, stack, 
                                    comp, k, lastPtr, cnt, liveVal, targetIdx, 
                                    newNode, parentIdx, path, curr, loopStep, 
                                    targetComp, newVal, success >>

ClickOp(self) == /\ pc[self] = "ClickOp"
                 /\ IF COUNT < MaxClock
                       THEN /\ COUNT' = COUNT + 1
                            /\ history' = [c \in Components |-> [history[c] EXCEPT ![COUNT'] = {c_val[c]}]]
                       ELSE /\ TRUE
                            /\ UNCHANGED << COUNT, history >>
                 /\ pc' = [pc EXCEPT ![self] = "ClientLoop"]
                 /\ UNCHANGED << c_val, c_nodeCount, c_deleted, heap, freePtr, 
                                 rootPtr, stack, comp, k, lastPtr, cnt, 
                                 liveVal, targetIdx, newNode, parentIdx, path, 
                                 curr, loopStep, targetComp, newVal, success, 
                                 ops >>

Update_Select(self) == /\ pc[self] = "Update_Select"
                       /\ \E c \in Components:
                            \E v \in Values:
                              /\ targetComp' = [targetComp EXCEPT ![self] = c]
                              /\ newVal' = [newVal EXCEPT ![self] = v]
                       /\ pc' = [pc EXCEPT ![self] = "Update_Catchup"]
                       /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                       history, heap, freePtr, rootPtr, stack, 
                                       comp, k, lastPtr, cnt, liveVal, 
                                       targetIdx, newNode, parentIdx, path, 
                                       curr, loopStep, success, ops >>

Update_Catchup(self) == /\ pc[self] = "Update_Catchup"
                        /\ /\ comp' = [comp EXCEPT ![self] = targetComp[self]]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CatchUpTreeProc",
                                                                    pc        |->  "Update_RetryCatchup",
                                                                    k         |->  k[self],
                                                                    lastPtr   |->  lastPtr[self],
                                                                    cnt       |->  cnt[self],
                                                                    liveVal   |->  liveVal[self],
                                                                    targetIdx |->  targetIdx[self],
                                                                    newNode   |->  newNode[self],
                                                                    parentIdx |->  parentIdx[self],
                                                                    path      |->  path[self],
                                                                    curr      |->  curr[self],
                                                                    loopStep  |->  loopStep[self],
                                                                    comp      |->  comp[self] ] >>
                                                                \o stack[self]]
                        /\ k' = [k EXCEPT ![self] = 1]
                        /\ lastPtr' = [lastPtr EXCEPT ![self] = Null]
                        /\ cnt' = [cnt EXCEPT ![self] = 0]
                        /\ liveVal' = [liveVal EXCEPT ![self] = Bot]
                        /\ targetIdx' = [targetIdx EXCEPT ![self] = 0]
                        /\ newNode' = [newNode EXCEPT ![self] = Null]
                        /\ parentIdx' = [parentIdx EXCEPT ![self] = 0]
                        /\ path' = [path EXCEPT ![self] = <<>>]
                        /\ curr' = [curr EXCEPT ![self] = Null]
                        /\ loopStep' = [loopStep EXCEPT ![self] = 1]
                        /\ pc' = [pc EXCEPT ![self] = "CatchUp_Check"]
                        /\ UNCHANGED << COUNT, c_val, c_nodeCount, c_deleted, 
                                        history, heap, freePtr, rootPtr, 
                                        targetComp, newVal, success, ops >>

Update_RetryCatchup(self) == /\ pc[self] = "Update_RetryCatchup"
                             /\ IF ~success[self]
                                   THEN /\ /\ comp' = [comp EXCEPT ![self] = targetComp[self]]
                                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CatchUpTreeProc",
                                                                                    pc        |->  "Update_Apply",
                                                                                    k         |->  k[self],
                                                                                    lastPtr   |->  lastPtr[self],
                                                                                    cnt       |->  cnt[self],
                                                                                    liveVal   |->  liveVal[self],
                                                                                    targetIdx |->  targetIdx[self],
                                                                                    newNode   |->  newNode[self],
                                                                                    parentIdx |->  parentIdx[self],
                                                                                    path      |->  path[self],
                                                                                    curr      |->  curr[self],
                                                                                    loopStep  |->  loopStep[self],
                                                                                    comp      |->  comp[self] ] >>
                                                                                \o stack[self]]
                                        /\ k' = [k EXCEPT ![self] = 1]
                                        /\ lastPtr' = [lastPtr EXCEPT ![self] = Null]
                                        /\ cnt' = [cnt EXCEPT ![self] = 0]
                                        /\ liveVal' = [liveVal EXCEPT ![self] = Bot]
                                        /\ targetIdx' = [targetIdx EXCEPT ![self] = 0]
                                        /\ newNode' = [newNode EXCEPT ![self] = Null]
                                        /\ parentIdx' = [parentIdx EXCEPT ![self] = 0]
                                        /\ path' = [path EXCEPT ![self] = <<>>]
                                        /\ curr' = [curr EXCEPT ![self] = Null]
                                        /\ loopStep' = [loopStep EXCEPT ![self] = 1]
                                        /\ pc' = [pc EXCEPT ![self] = "CatchUp_Check"]
                                   ELSE /\ pc' = [pc EXCEPT ![self] = "Update_Apply"]
                                        /\ UNCHANGED << stack, comp, k, 
                                                        lastPtr, cnt, liveVal, 
                                                        targetIdx, newNode, 
                                                        parentIdx, path, curr, 
                                                        loopStep >>
                             /\ UNCHANGED << COUNT, c_val, c_nodeCount, 
                                             c_deleted, history, heap, freePtr, 
                                             rootPtr, targetComp, newVal, 
                                             success, ops >>

Update_Apply(self) == /\ pc[self] = "Update_Apply"
                      /\ c_val' = [c_val EXCEPT ![targetComp[self]] = newVal[self]]
                      /\ IF COUNT > 0
                            THEN /\ history' = [history EXCEPT ![targetComp[self]][COUNT] = history[targetComp[self]][COUNT] \cup {newVal[self]}]
                            ELSE /\ TRUE
                                 /\ UNCHANGED history
                      /\ pc' = [pc EXCEPT ![self] = "ClientLoop"]
                      /\ UNCHANGED << COUNT, c_nodeCount, c_deleted, heap, 
                                      freePtr, rootPtr, stack, comp, k, 
                                      lastPtr, cnt, liveVal, targetIdx, 
                                      newNode, parentIdx, path, curr, loopStep, 
                                      targetComp, newVal, success, ops >>

Client(self) == ClientLoop(self) \/ ClickOp(self) \/ Update_Select(self)
                   \/ Update_Catchup(self) \/ Update_RetryCatchup(self)
                   \/ Update_Apply(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: CatchUpTreeProc(self))
           \/ (\E self \in Threads: Client(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

\* -------------------------------------------------------------------------
\* CUSTOM INVARIANTS FOR PHYSICAL VERIFICATION
\* -------------------------------------------------------------------------
\* -------------------------------------------------------------------------
\* CUSTOM INVARIANTS FOR PHYSICAL VERIFICATION
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

=============================================================================
