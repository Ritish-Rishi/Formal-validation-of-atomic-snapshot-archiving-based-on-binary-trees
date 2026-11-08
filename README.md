# SnapArchTree: Formal Verification and Empirical Evaluation of Binary Tree-Based Archival of Atomic Snapshots

This repository contains the formal verification specifications (**PlusCal / TLA+**) and empirical performance evaluation suite (**Java / JMH**) for **SnapArchTree**, a lock-free concurrent protocol for archiving and querying historical atomic snapshots using an implicit level-order complete binary tree.

This artifact accompanies the research paper:
> **"Formal Verification of Binary Tree-Based Archival of Atomic Snapshots"**  
> *FederatedHPC Workshop (co-located with IEEE HiPC 2026)*

---

## 1. Overview & Motivation

Traditional lock-free snapshot archival structures (such as **SnapArch**) store historical component states in a singly linked list. While linked lists support $O(1)$ tail appends via Compare-And-Swap (CAS) helping, answering historical point queries (`search(targetSnap)`) requires an $O(N)$ linear traversal from the head node.

**SnapArchTree** replaces the linear chain with an **implicit level-order complete binary tree**:
* **Implicit Bitwise Routing (`GetPhysicalNode`):** Nodes are indexed in 1-based level order (`1..nodeCount`). Any node at index $k$ is reached from the root (`index 1`) in $O(\log N)$ steps by inspecting the binary bits of $k$ from the second most significant bit down to the least significant bit (`0` $\rightarrow$ `left`, `1` $\rightarrow$ `right`).
* **Lock-Free Cooperative Helping (`CatchUpTree`):** Concurrent mutators and observers cooperatively append new snapshot epochs at `nodeCount + 1` using two-phase CAS helping—first linking the physical child reference (`parent.left` or `parent.right`) and then advancing `nodeCount`—guaranteeing lock-free system-wide progress and strictly monotonic snapshot epochs across level-order indices.
* **Wait-Free Logarithmic Point Queries (`SearchTree`):** Because snapshot epochs are monotonically non-decreasing in level-order index space, historical Least-Upper-Bound (LUB) queries execute a binary search over `[1..nodeCount]`. Each binary search probe routes from the root in $O(\log N)$ pointer hops, reducing total query complexity from $O(N)$ to **$O(\log^2 N)$** ($33.65\times$ faster latency and $41.17\times$ fewer pointer hops at $N = 16,384$).
* **Bounded-Prefix Global Snapshot Export:** Supports linearizable full-component archival export via bounded-prefix Breadth-First Search (BFS) up to `exportLimit = nodeCount`.

---

## 2. Repository Structure

```text
├── tla/
│   ├── SnapArchTree_Physical.tla      # 3-thread core mutator & physical topology verification harness
│   └── SnapArchTree_Search.tla        # Multi-value concurrent search, BFS export, & deletion harness
├── src/main/java/org/example/
│   ├── SnapArchPaperEvaluation.java   # Standalone benchmark (Latency, Throughput, Scalability, Memory)
│   └── SnapArchJmhBenchmark.java      # JMH microbenchmark harness
├── results/
│   └── snaparch_evaluation_results.csv # Raw empirical benchmark output data
├── pom.xml                            # Maven build configuration for JMH
└── README.md
```

---

## 3. Formal Verification (PlusCal / TLA+)

We use the **TLA+ Toolbox** and explicit-state model checker (**TLC**) to exhaustively verify structural integrity, lock-free CAS helping, monotonic epoch ordering, historical search linearizability, and concurrent deletion safety.

### Verification Harnesses & State-Space Summary

To maximize verification depth while avoiding combinatorial state-space explosion from orthogonal observer roles, verification is structured across two specialized harnesses:

| Specification File | Concurrent Roles Modeled | Model Constants | Execution Diameter | Total States Generated | Distinct Reachable States | Verification Status |
| :--- | :--- | :--- | :---: | :---: | :---: | :---: |
| **`SnapArchTree_Physical.tla`** | 3 Symmetrical Mutator Threads (`t1, t2, t3`) | `Components={101}`, `MaxClock=5`, `MaxNodes=7`, `Values={1}` | **101** | $>244,623,000$ | **90,241,964** | **Verified (0 Errors)** |
| **`SnapArchTree_Search.tla`** | 2 Symmetrical Mutators (`t1, t2`) + `Reader` + `Exporter` + `Deleter` + `LiveReader` | `Components={101}`, `MaxClock=6`, `MaxNodes=7`, `Values={1,2}` | **108** | **64,209,101** | **25,018,679** | **Verified (0 Errors)** |

### Key Verified Invariants
1. **`PointerIntegrityPhysical` & `CompleteBinaryTreeTopologyPhysical`:** Confirms that every allocated index $i \in 1..\mathit{nodeCount}$ is physically reachable from the root via bitwise routing, with no cycles, dangling pointers, or level-order gaps under 3-thread CAS contention.
2. **`MonotonicSnapshotsPhysical`:** Confirms that for any two tree indices $i < j \le \mathit{nodeCount}$, their snapshot timestamps satisfy $\mathit{snap}[i] \le \mathit{snap}[j]$, preserving the sorted invariant required for binary search without rebalancing.
3. **`SnapshotValueConsistencyPhysical`:** Verifies that every archived node's value belongs to the valid ground-truth history set recorded at or before its snapshot epoch.
4. **`SearchLinearizable`:** Verifies that concurrent wait-free binary search (`SearchTreeProc`) always returns a value matching the ground-truth Least-Upper-Bound (LUB) snapshot epoch in `history`, or `-99` if the component was concurrently marked deleted.
5. **`ExportPrefixSafety` & `LiveReaderSafety`:** Verifies that bounded-prefix BFS extraction returns a strictly monotonic sequence of historical states and properly terminates under concurrent updates and logical deletions.

### How to Run the TLA+ Specifications
1. Install the [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html) (v1.7.1 or later).
2. Open `SnapArchTree_Physical.tla` or `SnapArchTree_Search.tla` in the TLA+ Toolbox.
3. Press **`Ctrl+T`** (`File -> Translate PlusCal Algorithm`) to update the TLA+ translation block if modified.
4. Create a New Model and configure the declared constants as shown in the table above (setting `Threads` as a symmetrical model value set, and `Null`, `Bot`, `defaultInitValue` as model values).
5. Under the **Invariants** section of the model overview, add all safety invariants listed at the bottom of the `.tla` file and click **Run TLC** (`F11`).

---

## 4. Empirical Performance Evaluation (Java Benchmark Suite)

To evaluate runtime performance against the linked-list baseline (**SnapArch**), we provide a complete Java evaluation suite measuring:
1. **Historical Point-Query Latency (`ns/op`) & Pointer Hops (`hops/op`)** across archival depths $N \in \{64, 256, 1024, 4096, 16384\}$.
2. **Single-Threaded & Multi-Threaded Read/Write Throughput (`ops/sec`)** across $1, 2, 4, 8,$ and $16$ concurrent worker threads ($85\%$ historical search, $15\%$ component update + global clock click).
3. **Retained Heap Memory Footprint (`KB` and `Bytes/Node`)** across $10,000$ to $250,000$ archived nodes.

### Prerequisites
* **Java Development Kit (JDK):** JDK 17 or higher
* **Apache Maven:** 3.8+ (optional, required only for the standalone JMH runner)

### Quick Start: Running the Complete Evaluation Suite
You can compile and run `SnapArchPaperEvaluation.java` directly using `javac` and `java` (completes in ~60–90 seconds and automatically exports `snaparch_evaluation_results.csv`):

```bash
# Compile the benchmark suite
javac -d out src/main/java/org/example/SnapArchPaperEvaluation.java

# Run with 4GB heap allocation
java -Xms2G -Xmx4G -cp out org.example.SnapArchPaperEvaluation
```

### Running the JMH Microbenchmark (Optional)
```bash
mvn clean package
java -jar target/benchmarks.jar -rf csv -rff jmh_snaparch_results.csv
```

---

## 5. Summary of Empirical Results

### 5.1 Historical Point-Query Scaling ($N = 64$ to $16,384$)

| Archival Depth ($N$) | SnapArch Latency (ns/op) | SnapArchTree Latency (ns/op) | SnapArch Avg Hops | SnapArchTree Avg Hops | Hop Reduction | Latency Speedup |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **64** | 1,019.14 ns | 550.38 ns | 33.4 | 39.4 | $0.85\times$ | **1.85x** |
| **256** | 721.20 ns | 345.88 ns | 129.6 | 67.2 | $1.93\times$ | **2.09x** |
| **1,024** | 4,977.24 ns | 601.60 ns | 514.3 | 103.1 | $4.99\times$ | **8.27x** |
| **4,096** | 17,619.51 ns | 1,009.10 ns | 2,046.4 | 147.0 | $13.92\times$ | **17.46x** |
| **16,384** | 104,661.65 ns | 3,110.38 ns | 8,192.4 | 199.0 | $41.17\times$ | **33.65x** |

### 5.2 Multi-Threaded Concurrent Throughput ($85\%$ Search / $15\%$ Update+Click, $N_{\text{init}} = 2,048$)

| Worker Threads | SnapArch Throughput (ops/sec) | SnapArchTree Throughput (ops/sec) | Throughput Speedup |
| :---: | :---: | :---: | :---: |
| **1** | 90,928 | 1,350,240 | **14.85x** |
| **2** | 171,361 | 2,441,361 | **14.25x** |
| **4** | 407,504 | 3,941,163 | **9.67x** |
| **8** | 350,380 | 4,395,670 | **12.55x** |
| **16** | 344,717 | 3,820,374 | **11.08x** |

### 5.3 Retained Heap Memory Footprint

| Archived Nodes | SnapArch Heap (KB) | SnapArchTree Heap (KB) | SnapArch (Bytes/Node) | SnapArchTree (Bytes/Node) | Memory Ratio |
| :---: | :---: | :---: | :---: | :---: | :---: |
| **10,000** | 391.1 KB | 625.2 KB | 40.1 B | 64.0 B | **1.60x** |
| **50,000** | 1,989.8 KB | 3,189.0 KB | 40.8 B | 65.3 B | **1.60x** |
| **100,000** | 3,957.2 KB | 6,445.7 KB | 40.5 B | 66.0 B | **1.63x** |
| **250,000** | 9,972.2 KB | 16,000.9 KB | 40.8 B | 65.5 B | **1.60x** |

---

## 6. License

This project is released for academic and research reproducibility.
