# SnapArchTree: Formal Verification and Empirical Evaluation of Binary Tree-Based Archival of Atomic Snapshots

This repository contains the formal verification specifications (**PlusCal / TLA+**), the standalone empirical benchmark suite (**Java**), and the raw experimental datasets for **SnapArchTree**, a lock-free concurrent protocol for archiving and querying historical atomic snapshots using an implicit level-order complete binary tree.

This artifact accompanies the research paper:
> **"Formal verification of binary tree based archival of atomic snapshots"**  
> *FederatedHPC Workshop (co-located with IEEE HiPC 2026)*

---

## 1. Overview & Motivation

Traditional lock-free snapshot archival structures (such as **SnapArch**) store historical component states in a singly linked list. While linked lists support $\mathcal{O}(1)$ tail appends via Compare-And-Swap (CAS) helping, answering historical point queries (`Search(targetSnap)`) requires an $\mathcal{O}(s - t + 1) = \mathcal{O}(N)$ linear traversal from the head node.

**SnapArchTree** replaces the linear chain with an **implicit level-order complete binary tree**:
* **Implicit Bitwise Routing (`getNodeByIndex` / `GetPhysicalNode`):** Nodes are indexed in 1-based level order (`1..nodeCount`). Any node at index $k$ is reached from the root (`index 1`) in $\mathcal{O}(\log N)$ wait-free pointer hops by inspecting the binary bits of $k$ from the second most significant bit down to the least significant bit (`0` $\rightarrow$ `left`, `1` $\rightarrow$ `right`).
* **Lock-Free Cooperative Helping (`CatchUpTree`):** Concurrent mutators and observers cooperatively append new snapshot epochs at `nodeCount + 1` using two-phase CAS helping—first linking the physical child reference (`parent.left` or `parent.right`) and then advancing `nodeCount`—guaranteeing lock-free system-wide progress and strictly monotonic snapshot epochs across level-order indices without tree rotations.
* **Wait-Free Logarithmic Point Queries (`SearchTree`):** Because snapshot epochs are monotonically non-decreasing in level-order index space, historical Least-Upper-Bound (LUB) queries execute a binary search over `[1..nodeCount]`. Each of the $\mathcal{O}(\log N)$ binary search probes routes from the root in $\mathcal{O}(\log N)$ pointer hops, reducing total query complexity from $\mathcal{O}(N)$ to **$\mathcal{O}(\log^2 N)$** (**$68.94\times$ faster median latency** and **$41.23\times$ fewer pointer hops** at $N = 16,384$).
* **Bounded-Prefix Global Snapshot Export (`ExportSnapshot`):** Supports linearizable full-component archival extraction via bounded-prefix Breadth-First Search (BFS) up to `limit = nodeCount` in $\mathcal{O}(N)$ wait-free steps.

---

## 2. Repository Structure

All verification specifications, benchmark sources, and experimental outputs are located directly in the root directory:

```text
├── README.md                          # Artifact documentation and reproduction guide
├── SnapArchPaperEvaluation.java       # Standalone noise-hardened Java benchmark suite
├── SnapArchTree_Physical.tla          # 3-thread core mutator & physical topology TLA+ harness
├── SnapArchTree_Search.tla            # Multi-value concurrent search, BFS export, & deletion TLA+ harness
├── snaparch_environment.txt           # Recorded hardware, OS, and JVM execution environment
├── snaparch_evaluation_results.csv    # Aggregated summary metrics (median, mean, SD, CV%, speedup)
└── snaparch_raw_trials.csv            # Per-trial raw measurements across all experiments
```

---

## 3. Formal Verification (PlusCal / TLA+)

We use the **TLA+ Toolbox** and explicit-state model checker (**TLC**) to exhaustively verify structural integrity, lock-free CAS helping, index-order epoch monotonicity, historical search linearizability, bounded-prefix BFS export, and concurrent deletion safety.

### Verification Harnesses & State-Space Summary

| Specification File | Concurrent Roles Modeled | Model Constants | Execution Diameter | Total States Generated | Distinct Reachable States | Peak Queue | Verification Status |
| :--- | :--- | :--- | :---: | :---: | :---: | :---: | :---: |
| **`SnapArchTree_Physical.tla`** | 3 Symmetrical Mutator Threads (`t1, t2, t3`) | `Components={101}`, `MaxClock=5`, `MaxNodes=7`, `Values={1}` | **101** | $244,623,443$ | **90,241,964** | 1,678,843 | **Verified (0 Errors)** |
| **`SnapArchTree_Search.tla`** | 2 Symmetrical Mutators (`t1, t2`) + `Reader` + `Exporter` + `Deleter` + `LiveReader` | `Components={101}`, `MaxClock=6`, `MaxNodes=7`, `Values={1,2}` | **108** | **64,209,101** | **25,018,679** | 948,098 | **Verified (0 Errors)** |

### Key Verified Invariants (Lemmas 1–6)
1. **`PointerIntegrityPhysical` (Lemma 1):** Every dynamically allocated node in `1..(freePtr - 1)` has child pointers referencing valid allocated addresses, and unallocated heap slots retain `Null` pointers.
2. **`CompleteBinaryTreeTopologyPhysical` (Lemma 2):** Every sequential level-order index $i \in 1..\mathit{nodeCount}$ resolves to a valid physical node from the root, and every node $i \ge 2$ is directly linked from its structural parent $\lfloor i / 2 \rfloor$.
3. **`MonotonicSnapshotsPhysical` (Lemma 3):** For any pair of level-order indices $1 \le i < j \le \mathit{nodeCount}$, $\mathit{SnapNum}(\mathit{node}_i) \le \mathit{SnapNum}(\mathit{node}_j)$ (strictly $<$ under late sampling), establishing the sorted invariant required for binary search.
4. **`SnapshotValueConsistencyPhysical` (Lemma 4):** Every linked node's value belongs to the cumulative ground-truth history set $\bigcup_{t \in 0..s} \mathit{history}[c][t]$ recorded at or before its snapshot epoch $s$.
5. **`LiveReaderSafety` & `ExportPrefixSafety` (Lemma 5):** Concurrent live reads and bounded-prefix BFS exports linearize safely against updates and tombstone deletions (`c_deleted`), returning valid states or the deletion sentinel (`-99`, never $\bot$).
6. **`SearchLinearizable` (Lemma 6):** Every completed `SearchTreeProc` query returns either `-99` (if deleted) or a value present in the ground-truth `history[c][lubSnap]`, where `lubSnap` is the exact Least-Upper-Bound snapshot epoch $\ge \mathit{targetSnap}$.

### How to Run the TLA+ Specifications
1. Install the [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html) (v1.7.1 or later).
2. Open `SnapArchTree_Physical.tla` or `SnapArchTree_Search.tla` in the TLA+ Toolbox.
3. If modifying the PlusCal block, press **`Ctrl+T`** (`File -> Translate PlusCal Algorithm`) to update the TLA+ translation.
4. Create a New Model and configure the declared constants as shown in the table above (setting `Threads` as a symmetrical model value set, and `Null`, `Bot`, `defaultInitValue` as model values).
5. Add all safety invariants under the **Invariants** section of the model overview and click **Run TLC** (`F11`).

---

## 4. Empirical Performance Evaluation (Java Benchmark Suite)

`SnapArchPaperEvaluation.java` is a self-contained, zero-dependency Java evaluation suite comparing the linked-list baseline (**SnapArch**) against **SnapArchTree** across three experiments:
1. **Historical Point-Query Latency (`ns/op`), Read Throughput (`ops/sec`), & Pointer Hops (`hops/op`)** across archival depths $N \in \{64, 256, 1024, 4096, 16384\}$ ($T = 10$ alternating trials, $100,000$ random queries/trial).
2. **Multi-Threaded Concurrent Throughput (`ops/sec`)** across $1, 2, 4, 8,$ and $16$ worker threads ($85\%$ historical search, $15\%$ component update + global clock click, $1,000,000$ operations/trial across $T = 7$ alternating trials, $N_{\text{init}} = 2,048$).
3. **Retained Heap Memory Footprint (`KB` and `Bytes/Node`)** across $10,000, 50,000, 100,000,$ and $250,000$ archived nodes ($T = 5$ alternating repetitions with explicit GC settle barriers).

### Recorded Benchmark Environment (`snaparch_environment.txt`)
* **JVM:** Oracle Java HotSpot(TM) 64-Bit Server VM (JDK `23.0.2`, G1GC, ~2 GB Max Heap)
* **OS & Hardware:** Windows 11 10.0 (`amd64`), 8 Logical Processors
* **Parameters:** `trialsLatency=10`, `trialsThreads=7`, `trialsMemory=5`, `measureQueries=100000`, `warmupMs=1500`, `totalOps=1000000`, `warmupOps=150000`, `seed=20261107`

### How to Compile and Run the Benchmark

Because `SnapArchPaperEvaluation.java` declares `package org.example;`, compile it with `javac -d .` so the package directory structure is generated automatically:

```bash
# 1. Compile SnapArchPaperEvaluation.java into ./org/example/
javac -d . SnapArchPaperEvaluation.java

# 2. Run the full noise-hardened evaluation suite (writes CSV and environment files)
java -Xms2g -Xmx2g -cp . org.example.SnapArchPaperEvaluation

# Optional: Run a fast smoke test (~5 seconds)
java -Dquick=true -cp . org.example.SnapArchPaperEvaluation
```

Running the suite automatically generates `snaparch_evaluation_results.csv`, `snaparch_raw_trials.csv`, and `snaparch_environment.txt`.

---

## 5. Summary of Empirical Results (`snaparch_evaluation_results.csv`)

### 5.1 Historical Point-Query Scaling ($T = 10$ Trials, $100,000$ Queries/Trial)

| Archival Depth ($N$) | SnapArch Median (ns/op) | SnapArchTree Median (ns/op) | SnapArch Mean ± SD (ns/op) | SnapArchTree Mean ± SD (ns/op) | SnapArch Avg Hops | SnapArchTree Avg Hops | Hop Reduction | Latency Speedup |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **64** | 117.05 ns | 108.83 ns | 133.47 ± 34.43 | 133.87 ± 46.93 | 33.48 | 39.44 | $0.85\times$ | **1.08x** |
| **256** | 556.50 ns | 192.31 ns | 575.80 ± 155.02 | 217.58 ± 65.82 | 129.13 | 67.13 | $1.92\times$ | **2.89x** |
| **1,024** | 2,750.93 ns | 453.79 ns | 2,763.54 ± 225.27 | 465.37 ± 133.83 | 514.04 | 103.10 | $4.99\times$ | **6.06x** |
| **4,096** | 11,856.56 ns | 641.58 ns | 11,853.60 ± 665.83 | 667.36 ± 163.51 | 2,047.86 | 147.02 | $13.93\times$ | **18.48x** |
| **16,384** | 51,572.81 ns | 748.13 ns | 52,094.88 ± 2,062.39 | 873.17 ± 273.23 | 8,205.75 | 199.03 | $41.23\times$ | **68.94x** |

### 5.2 Multi-Threaded Concurrent Throughput ($85\%$ Search / $15\%$ Update+Click, $1\text{M}$ Ops/Run, $T = 7$ Trials)

| Worker Threads | SnapArch Median (ops/sec) | SnapArchTree Median (ops/sec) | SnapArch Mean ± SD (ops/sec) | SnapArchTree Mean ± SD (ops/sec) | List CV% | Tree CV% | Throughput Speedup |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **1** | 162,794 | 1,862,139 | 162,130 ± 3,224 | 1,877,621 ± 62,105 | 2.0% | 3.3% | **11.44x** |
| **2** | 329,831 | 3,188,017 | 329,391 ± 4,595 | 3,216,617 ± 132,576 | 1.4% | 4.1% | **9.67x** |
| **4** | 625,498 | 5,099,923 | 626,864 ± 8,927 | 4,968,274 ± 395,208 | 1.4% | 8.0% | **8.15x** |
| **8** | 1,067,907 | 5,913,021 | 1,069,702 ± 40,112 | 5,928,125 ± 418,843 | 3.7% | 7.1% | **5.54x** |
| **16** | 1,040,036 | 5,813,761 | 1,039,837 ± 35,631 | 5,815,089 ± 227,068 | 3.4% | 3.9% | **5.59x** |

### 5.3 Retained Heap Memory Footprint ($T = 5$ Repetitions)

| Archived Nodes | SnapArch Median Heap (KB) | SnapArchTree Median Heap (KB) | SnapArch (Bytes/Node) | SnapArchTree (Bytes/Node) | List CV% | Tree CV% | Memory Ratio |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **10,000** | 390.80 KB | 625.19 KB | 40.02 B | 64.02 B | 0.0% | 0.0% | **1.60x** |
| **50,000** | 1,993.84 KB | 3,170.19 KB | 40.83 B | 64.93 B | 0.9% | 1.0% | **1.59x** |
| **100,000** | 3,937.67 KB | 6,380.05 KB | 40.32 B | 65.33 B | 0.6% | 0.6% | **1.62x** |
| **250,000** | 9,968.66 KB | 16,028.86 KB | 40.83 B | 65.65 B | 0.2% | 0.1% | **1.61x** |

---

## 6. License

This artifact is released for academic and research reproducibility.
