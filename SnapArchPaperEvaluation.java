package org.example;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.management.ManagementFactory;
import java.lang.management.GarbageCollectorMXBean;
import java.lang.management.MemoryMXBean;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.SplittableRandom;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.AtomicReference;

public class SnapArchPaperEvaluation {

    // Prevents JVM Dead-Code Elimination (DCE) like JMH Blackhole
    public static volatile long BLACKHOLE = 0;

    // =========================================================================
    // 1. BASELINE: SnapArch (Lock-Free Linked-List Snapshot Archival)
    // =========================================================================
    static class SnapArchList {
        static class ListNode {
            final int snapNum;
            final int val;
            final AtomicReference<ListNode> next = new AtomicReference<>(null);

            ListNode(int snapNum, int val) {
                this.snapNum = snapNum;
                this.val = val;
            }
        }

        static class ComponentState {
            volatile int currentVal;
            final AtomicBoolean deleted = new AtomicBoolean(false);
            final ListNode head;
            final AtomicReference<ListNode> tail;
            final AtomicInteger nodeCount = new AtomicInteger(1);

            ComponentState(int initVal) {
                this.currentVal = initVal;
                this.head = new ListNode(0, initVal);
                this.tail = new AtomicReference<>(this.head);
            }
        }

        final AtomicInteger globalClock = new AtomicInteger(0);
        final ComponentState[] components;

        SnapArchList(int numComponents, int initVal) {
            components = new ComponentState[numComponents];
            for (int i = 0; i < numComponents; i++) {
                components[i] = new ComponentState(initVal);
            }
        }

        void forceAppendForSetup(int compId, int snapNum, int val) {
            ComponentState comp = components[compId];
            ListNode currTail = comp.tail.get();
            if (currTail.snapNum < snapNum) {
                ListNode nextNode = new ListNode(snapNum, val);
                currTail.next.set(nextNode);
                comp.tail.set(nextNode);
                comp.nodeCount.incrementAndGet();
                globalClock.set(Math.max(globalClock.get(), snapNum));
            }
        }

        public void click() {
            globalClock.incrementAndGet();
        }

        public boolean catchUp(int compId) {
            ComponentState comp = components[compId];
            if (comp.deleted.get()) return false;

            int localCount = globalClock.get();
            ListNode currTail = comp.tail.get();
            ListNode nextNode = currTail.next.get();
            if (nextNode != null) {
                comp.tail.compareAndSet(currTail, nextNode);
                currTail = comp.tail.get();
            }

            if (currTail.snapNum < localCount) {
                int readVal = comp.currentVal;
                ListNode newNode = new ListNode(localCount, readVal);
                if (currTail.next.compareAndSet(null, newNode)) {
                    comp.tail.compareAndSet(currTail, newNode);
                    comp.nodeCount.incrementAndGet();
                    return true;
                } else {
                    comp.tail.compareAndSet(currTail, currTail.next.get());
                    return false;
                }
            }
            return true;
        }

        public void update(int compId, int newVal) {
            ComponentState comp = components[compId];
            if (comp.deleted.get()) return;
            catchUp(compId);
            if (!comp.deleted.get()) {
                catchUp(compId);
                comp.currentVal = newVal;
            }
        }

        public int search(int compId, int targetSnap, AtomicLong hopsCounter) {
            ComponentState comp = components[compId];
            if (comp.deleted.get()) return -99;

            if (targetSnap > comp.tail.get().snapNum) {
                catchUp(compId);
                if (targetSnap > comp.tail.get().snapNum) {
                    catchUp(compId);
                }
            }

            ListNode curr = comp.head;
            int closestVal = curr.val;
            long hops = 0;
            while (curr != null) {
                hops++;
                if (curr.snapNum >= targetSnap) {
                    if (hopsCounter != null) hopsCounter.addAndGet(hops);
                    return curr.val;
                }
                closestVal = curr.val;
                curr = curr.next.get();
            }
            if (hopsCounter != null) hopsCounter.addAndGet(hops);
            return closestVal;
        }
    }

    // =========================================================================
    // 2. PROPOSED: SnapArchTree (Lock-Free Complete Binary Tree Archival)
    // =========================================================================
    static class SnapArchTree {
        static class TreeNode {
            final int snapNum;
            final int val;
            final AtomicReference<TreeNode> left = new AtomicReference<>(null);
            final AtomicReference<TreeNode> right = new AtomicReference<>(null);

            TreeNode(int snapNum, int val) {
                this.snapNum = snapNum;
                this.val = val;
            }
        }

        static class ComponentState {
            volatile int currentVal;
            final AtomicBoolean deleted = new AtomicBoolean(false);
            final TreeNode root;
            final AtomicInteger nodeCount = new AtomicInteger(1);

            ComponentState(int initVal) {
                this.currentVal = initVal;
                this.root = new TreeNode(0, initVal);
            }
        }

        final AtomicInteger globalClock = new AtomicInteger(0);
        final ComponentState[] components;

        SnapArchTree(int numComponents, int initVal) {
            components = new ComponentState[numComponents];
            for (int i = 0; i < numComponents; i++) {
                components[i] = new ComponentState(initVal);
            }
        }

        void forceAppendForSetup(int compId, int snapNum, int val) {
            ComponentState comp = components[compId];
            int currSize = comp.nodeCount.get();
            TreeNode lastNode = getPhysicalNode(comp.root, currSize, null);
            if (lastNode.snapNum < snapNum) {
                int targetIdx = currSize + 1;
                TreeNode parent = getPhysicalNode(comp.root, targetIdx >> 1, null);
                TreeNode newNode = new TreeNode(snapNum, val);
                if ((targetIdx & 1) == 0) {
                    parent.left.set(newNode);
                } else {
                    parent.right.set(newNode);
                }
                comp.nodeCount.set(targetIdx);
                globalClock.set(Math.max(globalClock.get(), snapNum));
            }
        }

        public void click() {
            globalClock.incrementAndGet();
        }

        public TreeNode getPhysicalNode(TreeNode root, int targetIndex, AtomicLong hopsCounter) {
            if (targetIndex <= 1 || root == null) {
                if (hopsCounter != null) hopsCounter.incrementAndGet();
                return root;
            }
            TreeNode curr = root;
            int highestBit = Integer.highestOneBit(targetIndex);
            long hops = 1;
            for (int mask = highestBit >> 1; mask > 0 && curr != null; mask >>= 1) {
                hops++;
                if ((targetIndex & mask) == 0) {
                    curr = curr.left.get();
                } else {
                    curr = curr.right.get();
                }
            }
            if (hopsCounter != null) hopsCounter.addAndGet(hops);
            return curr;
        }

        public boolean catchUpTree(int compId) {
            ComponentState comp = components[compId];
            if (comp.deleted.get()) return false;

            int localCount = globalClock.get();
            int currSize = comp.nodeCount.get();
            TreeNode lastNode = getPhysicalNode(comp.root, currSize, null);

            int nextIndex = currSize + 1;
            TreeNode parentOfNext = getPhysicalNode(comp.root, nextIndex >> 1, null);
            if (parentOfNext != null) {
                TreeNode existingChild = ((nextIndex & 1) == 0)
                        ? parentOfNext.left.get()
                        : parentOfNext.right.get();
                if (existingChild != null) {
                    comp.nodeCount.compareAndSet(currSize, nextIndex);
                    currSize = comp.nodeCount.get();
                    lastNode = getPhysicalNode(comp.root, currSize, null);
                }
            }

            if (lastNode != null && lastNode.snapNum < localCount) {
                int readVal = comp.currentVal;
                int targetIdx = currSize + 1;
                TreeNode parent = getPhysicalNode(comp.root, targetIdx >> 1, null);
                if (parent == null) return false;

                TreeNode newNode = new TreeNode(localCount, readVal);
                boolean casSuccess;
                if ((targetIdx & 1) == 0) {
                    casSuccess = parent.left.compareAndSet(null, newNode);
                } else {
                    casSuccess = parent.right.compareAndSet(null, newNode);
                }
                comp.nodeCount.compareAndSet(currSize, targetIdx);
                return casSuccess;
            }
            return true;
        }

        public void update(int compId, int newVal) {
            ComponentState comp = components[compId];
            if (comp.deleted.get()) return;
            catchUpTree(compId);
            if (!comp.deleted.get()) {
                catchUpTree(compId);
                comp.currentVal = newVal;
            }
        }

        public int searchTree(int compId, int targetSnap, AtomicLong hopsCounter) {
            ComponentState comp = components[compId];
            if (comp.deleted.get()) return -99;

            int currSize = comp.nodeCount.get();
            TreeNode highestNode = getPhysicalNode(comp.root, currSize, hopsCounter);
            if (highestNode != null && targetSnap > highestNode.snapNum) {
                catchUpTree(compId);
                currSize = comp.nodeCount.get();
                highestNode = getPhysicalNode(comp.root, currSize, hopsCounter);
                if (highestNode != null && targetSnap > highestNode.snapNum) {
                    catchUpTree(compId);
                    currSize = comp.nodeCount.get();
                    highestNode = getPhysicalNode(comp.root, currSize, hopsCounter);
                }
            }

            int low = 1;
            int high = comp.nodeCount.get();
            // Default fallback if targetSnap > all nodes in the tree is the latest node's value
            int closestMatchVal = (highestNode != null) ? highestNode.val : comp.root.val;

            while (low <= high) {
                int mid = (low + high) >>> 1;
                TreeNode midNode = getPhysicalNode(comp.root, mid, hopsCounter);
                if (midNode == null) {
                    high = mid - 1;
                } else if (midNode.snapNum >= targetSnap) {
                    closestMatchVal = midNode.val; // Valid LUB candidate (>= targetSnap)
                    high = mid - 1;                // Try to find an earlier snapshot still >= targetSnap
                } else {
                    low = mid + 1;                 // Too old (< targetSnap): do NOT overwrite closestMatchVal!
                }
            }
            return closestMatchVal;
        }
    }

    // =========================================================================
    // 3. EVALUATION SUITE (noise-hardened version)
    //
    // Changes versus the original harness (data structures above are unchanged):
    //  - Per-configuration, time-based JIT warm-up (and a global warm-up first),
    //    so the first measured configuration is no longer cold.
    //  - Hop counting runs in a separate, untimed pass (it used to add AtomicLong
    //    overhead to the timed trial 0).
    //  - More trials; every trial is recorded and summarised with mean, standard
    //    deviation, median and coefficient of variation. Ratios use medians.
    //  - The order of list/tree alternates between trials (no fixed "list first").
    //  - Concurrent runs: warm-up per thread count, a start barrier that waits for
    //    all workers, 1M ops per run (was 160k), fixed seeds so list and tree see
    //    the same operation stream in a given trial.
    //  - Memory: repeated measurements, median reported.
    //  - Environment (JVM, cores, flags) written to snaparch_environment.txt.
    //
    // Recommended launch (fixed heap, no ergonomics surprises):
    //   java -Xms2g -Xmx2g -XX:+UseParallelGC -XX:+AlwaysPreTouch \
    //        -cp . org.example.SnapArchPaperEvaluation
    // Quick smoke test:  add  -Dquick=true
    // =========================================================================

    static final boolean QUICK = Boolean.getBoolean("quick");
    static final int TRIALS_LATENCY = Integer.getInteger("trialsLatency", QUICK ? 3 : 10);
    static final int TRIALS_THREADS = Integer.getInteger("trialsThreads", QUICK ? 2 : 7);
    static final int TRIALS_MEMORY = Integer.getInteger("trialsMemory", QUICK ? 2 : 5);
    static final int MEASURE_QUERIES = Integer.getInteger("measureQueries", QUICK ? 5_000 : 100_000);
    static final long WARMUP_MS = Long.getLong("warmupMs", QUICK ? 100 : 1500);
    static final int TOTAL_OPS = Integer.getInteger("totalOps", QUICK ? 20_000 : 1_000_000);
    static final int WARMUP_OPS = Integer.getInteger("warmupOps", QUICK ? 5_000 : 150_000);
    static final long SEED = Long.getLong("seed", 20261107L);

    static final String SUMMARY_HEADER =
            "Experiment,Parameter,List_Median,Tree_Median,List_Mean,Tree_Mean,"
                    + "List_StdDev,Tree_StdDev,List_CV_pct,Tree_CV_pct,Trials,Unit,Ratio_Median";
    static final String RAW_HEADER = "Experiment,Parameter,Trial,Structure,Value,Unit";

    static final class Stats {
        final int n;
        final double mean, sd, median, min, max;

        Stats(double[] xs) {
            n = xs.length;
            double[] s = xs.clone();
            Arrays.sort(s);
            double sum = 0;
            for (double x : xs) sum += x;
            mean = sum / n;
            double ss = 0;
            for (double x : xs) ss += (x - mean) * (x - mean);
            sd = n > 1 ? Math.sqrt(ss / (n - 1)) : 0.0;
            median = (n % 2 == 1) ? s[n / 2] : 0.5 * (s[n / 2 - 1] + s[n / 2]);
            min = s[0];
            max = s[n - 1];
        }

        double cvPct() {
            return mean == 0 ? 0 : 100.0 * sd / mean;
        }
    }

    private static String summaryRow(String exp, String param, Stats list, Stats tree,
                                     String unit, double ratio) {
        return String.format(Locale.US, "%s,%s,%.2f,%.2f,%.2f,%.2f,%.2f,%.2f,%.1f,%.1f,%d,%s,%.2fx",
                exp, param, list.median, tree.median, list.mean, tree.mean,
                list.sd, tree.sd, list.cvPct(), tree.cvPct(), list.n, unit, ratio);
    }

    private static Stats single(double v) {
        return new Stats(new double[]{v});
    }

    public static void main(String[] args) throws Exception {
        List<String> summary = new ArrayList<>();
        List<String> raw = new ArrayList<>();
        summary.add(SUMMARY_HEADER);
        raw.add(RAW_HEADER);

        System.out.println("==============================================================================================");
        System.out.println("  SNAPARCH vs. SNAPARCHTREE: EMPIRICAL EVALUATION SUITE (noise-hardened)");
        System.out.println("==============================================================================================");
        writeEnvironment();

        System.out.println("\n[warm-up] global JIT warm-up ...");
        globalWarmup();

        runExperiment1_SearchLatency(summary, raw);
        System.out.println();
        runExperiment2_ThreadScalability(summary, raw);
        System.out.println();
        runExperiment3_MemoryFootprint(summary, raw);

        writeLines("snaparch_evaluation_results.csv", summary);
        writeLines("snaparch_raw_trials.csv", raw);
        System.out.println("\n[SUCCESS] Wrote snaparch_evaluation_results.csv, snaparch_raw_trials.csv, "
                + "snaparch_environment.txt");
    }

    private static void writeLines(String file, List<String> lines) throws IOException {
        try (PrintWriter pw = new PrintWriter(new FileWriter(file))) {
            for (String l : lines) pw.println(l);
        }
    }

    private static void writeEnvironment() throws IOException {
        List<String> env = new ArrayList<>();
        env.add("java.version=" + System.getProperty("java.version"));
        env.add("java.vm.name=" + System.getProperty("java.vm.name"));
        env.add("java.vendor=" + System.getProperty("java.vendor"));
        env.add("os=" + System.getProperty("os.name") + " " + System.getProperty("os.version")
                + " (" + System.getProperty("os.arch") + ")");
        env.add("availableProcessors=" + Runtime.getRuntime().availableProcessors());
        env.add("maxHeapMB=" + Runtime.getRuntime().maxMemory() / (1024 * 1024));
        StringBuilder gcs = new StringBuilder();
        for (GarbageCollectorMXBean gc : ManagementFactory.getGarbageCollectorMXBeans()) {
            gcs.append(gc.getName()).append(' ');
        }
        env.add("garbageCollectors=" + gcs.toString().trim());
        env.add("jvmArgs=" + ManagementFactory.getRuntimeMXBean().getInputArguments());
        env.add("quick=" + QUICK + " trialsLatency=" + TRIALS_LATENCY + " trialsThreads=" + TRIALS_THREADS
                + " trialsMemory=" + TRIALS_MEMORY + " measureQueries=" + MEASURE_QUERIES
                + " warmupMs=" + WARMUP_MS + " totalOps=" + TOTAL_OPS + " warmupOps=" + WARMUP_OPS
                + " seed=" + SEED);
        writeLines("snaparch_environment.txt", env);
        System.out.println("[environment]");
        for (String e : env) System.out.println("  " + e);
        if (Runtime.getRuntime().availableProcessors() < 16) {
            System.out.println("  NOTE: fewer than 16 hardware threads; the 16-thread run is oversubscribed.");
        }
    }

    // -------------------------------------------------------------------------
    // Global warm-up: exercise search / update / click on both structures
    // -------------------------------------------------------------------------
    private static void globalWarmup() throws InterruptedException {
        SnapArchList l = new SnapArchList(4, 1);
        SnapArchTree t = new SnapArchTree(4, 1);
        for (int c = 0; c < 4; c++) {
            for (int i = 1; i <= 512; i++) {
                l.forceAppendForSetup(c, i, i * 10);
                t.forceAppendForSetup(c, i, i * 10);
            }
        }
        runConcurrentWorkers(2, Math.max(1000, WARMUP_OPS / 2), 1024, l, null, SEED);
        runConcurrentWorkers(2, Math.max(1000, WARMUP_OPS / 2), 1024, null, t, SEED);
    }

    // -------------------------------------------------------------------------
    // EXPERIMENT 1: Search latency, read throughput, pointer hops (single thread)
    // -------------------------------------------------------------------------
    private static long runListQueries(SnapArchList a, int[] qs, int start, int count) {
        long c = 0;
        for (int i = start; i < start + count; i++) c += a.search(0, qs[i], null);
        return c;
    }

    private static long runTreeQueries(SnapArchTree a, int[] qs, int start, int count) {
        long c = 0;
        for (int i = start; i < start + count; i++) c += a.searchTree(0, qs[i], null);
        return c;
    }

    private static void runExperiment1_SearchLatency(List<String> summary, List<String> raw) {
        int[] depths = QUICK ? new int[]{64, 256, 1024} : new int[]{64, 256, 1024, 4096, 16384};

        System.out.println("--- [1] HISTORICAL SEARCH LATENCY (ns/op, median of " + TRIALS_LATENCY
                + " trials), HOPS, THROUGHPUT ---");
        System.out.printf("%-8s | %-12s %-12s | %-9s %-9s | %-10s %-10s | %-8s%n",
                "Depth(N)", "List(ns)", "Tree(ns)", "List CV%", "Tree CV%", "List hops", "Tree hops", "Speedup");
        System.out.println("-----------------------------------------------------------------------------------------");

        for (int n : depths) {
            SnapArchList listArch = new SnapArchList(1, 0);
            SnapArchTree treeArch = new SnapArchTree(1, 0);
            for (int i = 1; i <= n; i++) {
                listArch.forceAppendForSetup(0, i, i * 10);
                treeArch.forceAppendForSetup(0, i, i * 10);
            }

            SplittableRandom rng = new SplittableRandom(SEED + n);
            int[] queries = new int[MEASURE_QUERIES];
            for (int q = 0; q < MEASURE_QUERIES; q++) queries[q] = rng.nextInt(1, n + 1);

            // Untimed pass: hop counts and functional cross-check.
            AtomicLong listHopsCounter = new AtomicLong(0);
            AtomicLong treeHopsCounter = new AtomicLong(0);
            long chkList = 0, chkTree = 0;
            for (int q = 0; q < MEASURE_QUERIES; q++) {
                chkList += listArch.search(0, queries[q], listHopsCounter);
                chkTree += treeArch.searchTree(0, queries[q], treeHopsCounter);
            }
            if (chkList != chkTree) {
                throw new AssertionError("Result mismatch between list and tree at N=" + n);
            }
            double listHops = (double) listHopsCounter.get() / MEASURE_QUERIES;
            double treeHops = (double) treeHopsCounter.get() / MEASURE_QUERIES;

            // Time-based warm-up for this depth (both structures).
            int chunk = Math.min(1000, MEASURE_QUERIES);
            long warmEnd = System.nanoTime() + WARMUP_MS * 1_000_000L;
            long sink = 0;
            int iter = 0;
            while (System.nanoTime() < warmEnd) {
                int start = (int) (((long) iter * chunk) % (MEASURE_QUERIES - chunk + 1));
                sink += runListQueries(listArch, queries, start, chunk);
                sink += runTreeQueries(treeArch, queries, start, chunk);
                iter++;
            }
            BLACKHOLE += sink;

            double[] listLat = new double[TRIALS_LATENCY];
            double[] treeLat = new double[TRIALS_LATENCY];
            for (int t = 0; t < TRIALS_LATENCY; t++) {
                boolean listFirst = (t % 2 == 0);
                long listNs, treeNs, cList, cTree;
                if (listFirst) {
                    long t0 = System.nanoTime();
                    cList = runListQueries(listArch, queries, 0, MEASURE_QUERIES);
                    listNs = System.nanoTime() - t0;
                    long t1 = System.nanoTime();
                    cTree = runTreeQueries(treeArch, queries, 0, MEASURE_QUERIES);
                    treeNs = System.nanoTime() - t1;
                } else {
                    long t1 = System.nanoTime();
                    cTree = runTreeQueries(treeArch, queries, 0, MEASURE_QUERIES);
                    treeNs = System.nanoTime() - t1;
                    long t0 = System.nanoTime();
                    cList = runListQueries(listArch, queries, 0, MEASURE_QUERIES);
                    listNs = System.nanoTime() - t0;
                }
                if (cList != cTree) {
                    throw new AssertionError("Result mismatch between list and tree at N=" + n);
                }
                BLACKHOLE += (cList ^ cTree);
                listLat[t] = (double) listNs / MEASURE_QUERIES;
                treeLat[t] = (double) treeNs / MEASURE_QUERIES;
                raw.add(String.format(Locale.US, "Search_Latency,N=%d,%d,SnapArch,%.2f,ns/op", n, t, listLat[t]));
                raw.add(String.format(Locale.US, "Search_Latency,N=%d,%d,SnapArchTree,%.2f,ns/op", n, t, treeLat[t]));
            }

            Stats ls = new Stats(listLat);
            Stats ts = new Stats(treeLat);
            double[] listThruArr = new double[TRIALS_LATENCY];
            double[] treeThruArr = new double[TRIALS_LATENCY];
            for (int t = 0; t < TRIALS_LATENCY; t++) {
                listThruArr[t] = 1e9 / listLat[t];
                treeThruArr[t] = 1e9 / treeLat[t];
            }
            Stats lth = new Stats(listThruArr);
            Stats tth = new Stats(treeThruArr);

            System.out.printf(Locale.US, "%-8d | %12.1f %12.1f | %8.1f%% %8.1f%% | %10.1f %10.1f | %7.2fx%n",
                    n, ls.median, ts.median, ls.cvPct(), ts.cvPct(), listHops, treeHops, ls.median / ts.median);

            String p = "N=" + n;
            summary.add(summaryRow("Search_Latency", p, ls, ts, "ns/op", ls.median / ts.median));
            summary.add(summaryRow("Search_Throughput", p, lth, tth, "ops/sec", tth.median / lth.median));
            summary.add(summaryRow("Pointer_Hops", p, single(listHops), single(treeHops), "hops/op",
                    listHops / treeHops));
        }
    }

    // -------------------------------------------------------------------------
    // EXPERIMENT 2: Thread scalability (85% search / 15% update+click)
    // -------------------------------------------------------------------------
    private static final int INIT_SNAPSHOTS = 2048;
    private static final int MAX_SNAPSHOTS_CAP = 4096;

    private static SnapArchList newPopulatedList() {
        SnapArchList a = new SnapArchList(4, 1);
        for (int c = 0; c < 4; c++) {
            for (int i = 1; i <= INIT_SNAPSHOTS; i++) a.forceAppendForSetup(c, i, i * 10);
        }
        return a;
    }

    private static SnapArchTree newPopulatedTree() {
        SnapArchTree a = new SnapArchTree(4, 1);
        for (int c = 0; c < 4; c++) {
            for (int i = 1; i <= INIT_SNAPSHOTS; i++) a.forceAppendForSetup(c, i, i * 10);
        }
        return a;
    }

    private static void settle() throws InterruptedException {
        System.gc();
        Thread.sleep(50);
    }

    private static void runExperiment2_ThreadScalability(List<String> summary, List<String> raw)
            throws InterruptedException {
        int[] threadCounts = QUICK ? new int[]{1, 2} : new int[]{1, 2, 4, 8, 16};

        System.out.println("--- [2] THREAD SCALABILITY (85% Search / 15% Update+Click, N_init=" + INIT_SNAPSHOTS
                + ", clock cap=" + MAX_SNAPSHOTS_CAP + ", " + TOTAL_OPS + " ops/run, median of "
                + TRIALS_THREADS + " trials) ---");
        System.out.printf("%-8s | %-16s %-16s | %-9s %-9s | %-8s%n",
                "Threads", "List (ops/s)", "Tree (ops/s)", "List CV%", "Tree CV%", "Speedup");
        System.out.println("--------------------------------------------------------------------------------");

        for (int nt : threadCounts) {
            int opsPerThread = Math.max(1, TOTAL_OPS / nt);
            int warmPerThread = Math.max(500, WARMUP_OPS / nt);

            // Discarded warm-up at this thread count.
            runConcurrentWorkers(nt, warmPerThread, MAX_SNAPSHOTS_CAP, newPopulatedList(), null, SEED - 1);
            runConcurrentWorkers(nt, warmPerThread, MAX_SNAPSHOTS_CAP, null, newPopulatedTree(), SEED - 1);

            double[] listThru = new double[TRIALS_THREADS];
            double[] treeThru = new double[TRIALS_THREADS];
            long actualOps = (long) nt * opsPerThread;

            for (int trial = 0; trial < TRIALS_THREADS; trial++) {
                long seed = SEED + 1000L * nt + trial;
                boolean listFirst = (trial % 2 == 0);
                long listNs, treeNs;
                if (listFirst) {
                    SnapArchList l = newPopulatedList();
                    settle();
                    listNs = runConcurrentWorkers(nt, opsPerThread, MAX_SNAPSHOTS_CAP, l, null, seed);
                    SnapArchTree t = newPopulatedTree();
                    settle();
                    treeNs = runConcurrentWorkers(nt, opsPerThread, MAX_SNAPSHOTS_CAP, null, t, seed);
                } else {
                    SnapArchTree t = newPopulatedTree();
                    settle();
                    treeNs = runConcurrentWorkers(nt, opsPerThread, MAX_SNAPSHOTS_CAP, null, t, seed);
                    SnapArchList l = newPopulatedList();
                    settle();
                    listNs = runConcurrentWorkers(nt, opsPerThread, MAX_SNAPSHOTS_CAP, l, null, seed);
                }
                listThru[trial] = actualOps * 1e9 / listNs;
                treeThru[trial] = actualOps * 1e9 / treeNs;
                raw.add(String.format(Locale.US, "Thread_Scalability_Throughput,Threads=%d,%d,SnapArch,%.0f,ops/sec",
                        nt, trial, listThru[trial]));
                raw.add(String.format(Locale.US, "Thread_Scalability_Throughput,Threads=%d,%d,SnapArchTree,%.0f,ops/sec",
                        nt, trial, treeThru[trial]));
            }

            Stats ls = new Stats(listThru);
            Stats ts = new Stats(treeThru);
            System.out.printf(Locale.US, "%-8d | %16.0f %16.0f | %8.1f%% %8.1f%% | %7.2fx%n",
                    nt, ls.median, ts.median, ls.cvPct(), ts.cvPct(), ts.median / ls.median);
            summary.add(summaryRow("Thread_Scalability_Throughput", "Threads=" + nt, ls, ts, "ops/sec",
                    ts.median / ls.median));
        }
    }

    private static long runConcurrentWorkers(
            int numThreads, int opsPerThread, int maxCap,
            SnapArchList listArch, SnapArchTree treeArch, long seed) throws InterruptedException {

        final boolean isList = (listArch != null);
        CountDownLatch readyLatch = new CountDownLatch(numThreads);
        CountDownLatch startLatch = new CountDownLatch(1);
        CountDownLatch doneLatch = new CountDownLatch(numThreads);
        AtomicReference<Throwable> failure = new AtomicReference<>(null);

        for (int t = 0; t < numThreads; t++) {
            final long threadSeed = seed * 31 + t * 7919L;
            Thread worker = new Thread(() -> {
                try {
                    SplittableRandom rng = new SplittableRandom(threadSeed);
                    readyLatch.countDown();
                    startLatch.await();
                    long localSink = 0;
                    for (int i = 0; i < opsPerThread; i++) {
                        int compId = rng.nextInt(4);
                        int roll = rng.nextInt(100);
                        if (roll < 85) {
                            int maxClock = isList ? listArch.globalClock.get() : treeArch.globalClock.get();
                            int target = rng.nextInt(1, Math.max(2, maxClock + 1));
                            if (isList) {
                                localSink += listArch.search(compId, target, null);
                            } else {
                                localSink += treeArch.searchTree(compId, target, null);
                            }
                        } else {
                            if (isList) {
                                if (roll < 88 && listArch.globalClock.get() < maxCap) listArch.click();
                                listArch.update(compId, i);
                            } else {
                                if (roll < 88 && treeArch.globalClock.get() < maxCap) treeArch.click();
                                treeArch.update(compId, i);
                            }
                        }
                    }
                    BLACKHOLE += localSink;
                } catch (Throwable e) {
                    failure.compareAndSet(null, e);
                } finally {
                    doneLatch.countDown();
                }
            });
            worker.setDaemon(true);
            worker.start();
        }

        readyLatch.await();
        long startNs = System.nanoTime();
        startLatch.countDown();
        doneLatch.await();
        long elapsed = System.nanoTime() - startNs;
        if (failure.get() != null) {
            throw new RuntimeException("Worker failed", failure.get());
        }
        return elapsed;
    }

    // -------------------------------------------------------------------------
    // EXPERIMENT 3: Memory (retained heap, bytes per node)
    // -------------------------------------------------------------------------
    private static void runExperiment3_MemoryFootprint(List<String> summary, List<String> raw)
            throws InterruptedException {
        int[] totalNodesList = QUICK ? new int[]{10_000, 50_000} : new int[]{10_000, 50_000, 100_000, 250_000};

        System.out.println("--- [3] MEMORY (retained heap after GC, median of " + TRIALS_MEMORY + " repetitions) ---");
        System.out.printf("%-12s | %-14s %-14s | %-12s %-12s | %-9s%n",
                "Nodes", "List (KB)", "Tree (KB)", "List B/node", "Tree B/node", "Ratio");
        System.out.println("-----------------------------------------------------------------------------------");

        MemoryMXBean memBean = ManagementFactory.getMemoryMXBean();

        for (int numNodes : totalNodesList) {
            double[] listBytes = new double[TRIALS_MEMORY];
            double[] treeBytes = new double[TRIALS_MEMORY];
            for (int rep = 0; rep < TRIALS_MEMORY; rep++) {
                boolean listFirst = (rep % 2 == 0);
                if (listFirst) {
                    listBytes[rep] = measureListBytes(memBean, numNodes);
                    treeBytes[rep] = measureTreeBytes(memBean, numNodes);
                } else {
                    treeBytes[rep] = measureTreeBytes(memBean, numNodes);
                    listBytes[rep] = measureListBytes(memBean, numNodes);
                }
                raw.add(String.format(Locale.US, "Memory_Retained_Bytes,Nodes=%d,%d,SnapArch,%.0f,bytes",
                        numNodes, rep, listBytes[rep]));
                raw.add(String.format(Locale.US, "Memory_Retained_Bytes,Nodes=%d,%d,SnapArchTree,%.0f,bytes",
                        numNodes, rep, treeBytes[rep]));
            }

            double[] listKb = new double[TRIALS_MEMORY];
            double[] treeKb = new double[TRIALS_MEMORY];
            double[] listPer = new double[TRIALS_MEMORY];
            double[] treePer = new double[TRIALS_MEMORY];
            for (int i = 0; i < TRIALS_MEMORY; i++) {
                listKb[i] = listBytes[i] / 1024.0;
                treeKb[i] = treeBytes[i] / 1024.0;
                listPer[i] = listBytes[i] / numNodes;
                treePer[i] = treeBytes[i] / numNodes;
            }
            Stats lkb = new Stats(listKb), tkb = new Stats(treeKb);
            Stats lpn = new Stats(listPer), tpn = new Stats(treePer);
            double ratio = tpn.median / lpn.median;

            System.out.printf(Locale.US, "%-12d | %14.1f %14.1f | %12.1f %12.1f | %8.2fx%n",
                    numNodes, lkb.median, tkb.median, lpn.median, tpn.median, ratio);

            summary.add(summaryRow("Memory_Retained_KB", "Nodes=" + numNodes, lkb, tkb, "KB", ratio));
            summary.add(summaryRow("Memory_Bytes_Per_Node", "Nodes=" + numNodes, lpn, tpn, "Bytes/Node", ratio));
        }
    }

    private static double measureListBytes(MemoryMXBean memBean, int numNodes) throws InterruptedException {
        forceGc(memBean);
        long base = getUsedHeapBytes(memBean);
        SnapArchList holder = new SnapArchList(1, 0);
        for (int i = 1; i <= numNodes; i++) holder.forceAppendForSetup(0, i, i);
        forceGc(memBean);
        long used = Math.max(1, getUsedHeapBytes(memBean) - base);
        BLACKHOLE += holder.components[0].nodeCount.get(); // keeps holder alive until here
        return used;
    }

    private static double measureTreeBytes(MemoryMXBean memBean, int numNodes) throws InterruptedException {
        forceGc(memBean);
        long base = getUsedHeapBytes(memBean);
        SnapArchTree holder = new SnapArchTree(1, 0);
        for (int i = 1; i <= numNodes; i++) holder.forceAppendForSetup(0, i, i);
        forceGc(memBean);
        long used = Math.max(1, getUsedHeapBytes(memBean) - base);
        BLACKHOLE += holder.components[0].nodeCount.get(); // keeps holder alive until here
        return used;
    }

    private static void forceGc(MemoryMXBean memBean) throws InterruptedException {
        for (int i = 0; i < 4; i++) {
            System.gc();
            memBean.gc();
            Thread.sleep(40);
        }
    }

    private static long getUsedHeapBytes(MemoryMXBean memBean) {
        return memBean.getHeapMemoryUsage().getUsed();
    }
}