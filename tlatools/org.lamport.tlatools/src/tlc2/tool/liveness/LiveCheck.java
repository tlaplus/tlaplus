// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:44 PST by lamport
//      modified on Thu Jan 10 18:41:04 PST 2002 by yuanyu

package tlc2.tool.liveness;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.StatePrinter;
import tlc2.tool.*;
import tlc2.tool.INextStateFunctor.InvariantViolatedException;
import tlc2.util.IStateWriter;
import tlc2.util.IStateWriter.Visualization;
import tlc2.util.LongVec;
import tlc2.util.NoopStateWriter;
import tlc2.util.SetOfStates;
import tlc2.util.statistics.IBucketStatistics;
import tlc2.value.impl.CounterExample;
import util.Assert;
import util.FatalException;

import java.io.IOException;
import java.util.*;
import java.util.concurrent.*;
import java.util.function.Supplier;

public class LiveCheck implements ILiveCheck {

    private final String metadir;
    private final IBucketStatistics outDegreeGraphStats;
    private final ILiveChecker[] checker;

    public LiveCheck(final ITool tool, final String mdir, final IBucketStatistics bucketStatistics) throws IOException {
        this(tool, Liveness.processLiveness(tool), mdir, bucketStatistics, new NoopStateWriter());
    }

    public LiveCheck(final ITool tool, final String mdir, final IBucketStatistics bucketStatistics, final IStateWriter stateWriter) throws IOException {
        this(tool, Liveness.processLiveness(tool), mdir, bucketStatistics, stateWriter);
    }

    public LiveCheck(final ITool tool, final OrderOfSolution[] solutions, final String mdir, final IBucketStatistics bucketStatistics) throws IOException {
        this(tool, solutions, mdir, bucketStatistics, new NoopLivenessStateWriter());
    }

    public LiveCheck(final ITool tool, final OrderOfSolution[] solutions, final String mdir, final IBucketStatistics bucketStatistics, final IStateWriter stateWriter) throws IOException {
        metadir = mdir;
        outDegreeGraphStats = bucketStatistics;
        checker = new ILiveChecker[solutions.length];
        for (int soln = 0; soln < solutions.length; soln++) {
            final ILivenessStateWriter writer = stateWriter.isNoop() || !stateWriter.isDot()
                    ? new NoopLivenessStateWriter()
                    : new DotLivenessStateWriter(stateWriter);
            if (!solutions[soln].hasTableau()) {
                checker[soln] = new LiveChecker(solutions[soln], soln, bucketStatistics, writer);
            } else {
                checker[soln] = new TableauLiveChecker(solutions[soln], soln, bucketStatistics, writer);
            }
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#addInitState(tlc2.tool.TLCState, long)
     */
    @Override
    public void addInitState(final ITool tool, final TLCState state, final long stateFP) {
        for (final ILiveChecker iLiveChecker : checker) {
            iLiveChecker.addInitState(tool, state, stateFP);
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#addNextState(tlc2.tool.TLCState, long, tlc2.util.SetOfStates)
     */
    @Override
    public void addNextState(final ITool tool, final TLCState s0, final long fp0, final SetOfStates nextStates) throws Exception {
        for (final ILiveChecker check : checker) {
            final OrderOfSolution oos = check.getSolution();
            final int alen = oos.getCheckAction().length;

            // Check the actions *before* the solution lock is acquired. This
            // increase concurrency as the lock on the OrderOfSolution is pretty
            // coarse grained (it essentially means we lock the complete
            // behavior graph (DiskGraph) just to add a single node). The
            // drawback is obviously, that we create a short-lived BitSet
            // to hold the result and loop over actions x successors twice
            // (here and down below). This is a little price to pay for significantly
            // increased concurrency.
            //
            // The actions have to be checked here because - in the light of
            // symmetry - while we still have access to the actual successor
            // state rather than just its fingerprint that represents all states
            // in the symmetry set. Unless super-symmetry is in place (the
            // actions checks for all states in the symmetry set evaluate to the
            // same value), the "smallest" (see
            // tlc2.tool.TLCStateMut.fingerPrint()) cannot be used as a
            // replacement state to check the actions.
            // TODO: In the past (commit 768b8e8), actions were only evaluated for nodes
            // that are new (ptr == -1)
            // (see https://github.com/tlaplus/tlaplus/issues/614)
            final BitSet checkActionResults = new BitSet(alen * nextStates.size());
            final var nextStatesIterator = nextStates.iterator();
            for (int sidx = 0; sidx < nextStates.size(); sidx++) {
                final TLCState s1 = nextStatesIterator.next();
                oos.checkAction(tool, s0, s1, checkActionResults, alen * sidx);
            }

            check.addNextState(tool, s0, fp0, nextStates, checkActionResults, oos.checkState(tool, s0));

            // Write the content of the current graph to a file in GraphViz
            // format. Useful when debugging!
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#doLiveCheck()
     */
    @Override
    public boolean doLiveCheck() {
        for (final ILiveChecker iLiveChecker : checker) {
            // If one of the disk graph's size has increased by the given
            // percentage, run liveness checking.
            //
            // TODO Alternatively:
            //
            // - LL suggest to dedicate a fixed fraction of model checking time
            // to liveness checking.
            //
            // - The level could be taken into account. Unless the level
            // (height) of the graph increases, no new cycle won't be found
            // anyway (all other aspects of liveness checking are checked as
            // part of regular safety checking).
            //
            // - The authors of the Divine model checker describe an algorithm
            // in http://dx.doi.org/10.1109/ASE.2003.1240299
            // that counts the "Back-level Edges" and runs liveness checking upon
            // a counter reaching a certain (user defined?!) threshold.
            //
            final AbstractDiskGraph diskGraph = iLiveChecker.getDiskGraph();
            final long sizeAtLastCheck = diskGraph.getSizeAtLastCheck();
            final long sizeCurrently = diskGraph.size();
            final double delta = (sizeCurrently - sizeAtLastCheck) / (sizeAtLastCheck * 1.d);
            if (delta > TLCGlobals.livenessThreshold) {
                return true;
            }
        }
        return false;
    }

    @Override
    public int check(final ITool tool, final boolean forceCheck) throws Exception {
        if (forceCheck) {
            return check0(tool, false);
        }
        if (!TLCGlobals.doLiveness()) {
            // The user requested to only check liveness once, on the complete
            // state graph.
            return EC.NO_ERROR;
        }
        for (final ILiveChecker iLiveChecker : checker) {
            // see note in doLiveCheck() above!
            final AbstractDiskGraph diskGraph = iLiveChecker.getDiskGraph();
            final long sizeAtLastCheck = diskGraph.getSizeAtLastCheck();
            final long sizeCurrently = diskGraph.size();
            final double delta = (sizeCurrently - sizeAtLastCheck) / (sizeAtLastCheck * 1.d);
            if (delta > TLCGlobals.livenessThreshold) {
                return check0(tool, false);
            }
        }
        return EC.NO_ERROR;
    }

    @Override
    public int finalCheck(final ITool tool) throws InterruptedException, IOException {

        // Do *not* re-create the nodePtrTable after the check which takes a
        // while for larger disk graphs.
        return check0(tool, true);
    }

    /**
     * @param finalCheck If the internal nodePtrTbl should be restored for a subsequent
     *                   liveness check. If this is the final/last check, it's pointless
     *                   to re-create the nodePtrTable.
     */
    protected int check0(final ITool tool, final boolean finalCheck) throws InterruptedException, IOException {
        final long startTime = System.currentTimeMillis();

        // Sum up the number of nodes in all disk graphs to indicate the amount
        // of work to be done by liveness checking.
        long sum = 0L;
        for (final ILiveChecker liveChecker : checker) {
            sum += liveChecker.getDiskGraph().size();
        }
        MP.printMessage(EC.TLC_CHECKING_TEMPORAL_PROPS, finalCheck ? "complete" : "current",
                Long.toString(sum), checker.length == 1 ? "" : checker.length + " branches of ");

        // Copy the array of checkers into a concurrent-enabled queue
        // that allows LiveWorker threads to easily get the next
        // LiveChecker to work on. We don't really need the FIFO
        // ordering of the BlockingQueue, just its support for removing
        // elements concurrently.
        //
        // Logically the queue is the unit of work the group of LiveWorkers
        // has to complete. Once the queue is empty, all work is done and
        // the LiveWorker threads will terminate.
        //
        // An alternative implementation could partition the array of
        // LiveChecker a-priori and assign one partition to each thread.
        // However, that assumes the work in all partitions is evenly
        // distributed, which is not necessarily true.
        final BlockingQueue<ILiveChecker> queue = new ArrayBlockingQueue<>(checker.length);
        queue.addAll(Arrays.asList(checker));


        /*
         * A LiveWorker below can either complete a unit of work a) without finding a
         * liveness violation, b) finds a violation, or c) fails to check because of an
         * exception/error (such as going out of memory). In case an LW fails to check,
         * we still wait for all other LWs to complete. A subset of the LWs might have
         * found a violation. In other words, the OOM of an LW has lower precedence than
         * a violation found by another LW. However, if any LW fails to check, we terminate
         * model checking after all LWs completed.
         */
        final int wNum = TLCGlobals.doSequentialLiveness() ? 1 : Math.min(checker.length, TLCGlobals.getNumWorkers());
        final ExecutorService pool = Executors.newFixedThreadPool(wNum);
        // CS is really just a container around the set of Futures returned by the pool. It saves us from
        // creating a low-level array.
        final CompletionService<Boolean> completionService = new ExecutorCompletionService<>(pool);

        final LiveWorkerSynchronization synchronization = new LiveWorkerSynchronization();

        for (int i = 0; i < wNum; i++) {
            completionService.submit(new LiveWorker(synchronization, tool, i, wNum, this, queue, finalCheck, tool.getMainChecker(), tool.getSimulator()));
        }
        // Wait for all LWs to complete.
        pool.shutdown();
        pool.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS); // wait forever

        // Check if any one of the LWs found a violation (ignore failures for now).
        ExecutionException ee = null;
        for (int i = 0; i < wNum; i++) {
            try {
                final Future<Boolean> future = completionService.take();
                if (future.get()) {
                    MP.printMessage(EC.TLC_CHECKING_TEMPORAL_PROPS_END,
                            TLC.convertRuntimeToHumanReadable(System.currentTimeMillis() - startTime));
                    return EC.TLC_TEMPORAL_PROPERTY_VIOLATED;
                }
            } catch (final ExecutionException e) {
                // handled below!
                ee = e;
            }
        }
        // Terminate if any one of the LWs failed c)
        if (ee != null) {
            final Throwable cause = ee.getCause();
            if (cause instanceof OutOfMemoryError) {
                MP.printError(EC.SYSTEM_OUT_OF_MEMORY_LIVENESS, cause);
            } else if (cause instanceof StackOverflowError) {
                MP.printError(EC.SYSTEM_STACK_OVERFLOW, cause);
            } else if (cause != null) {
                MP.printError(EC.GENERAL, cause);
            } else {
                MP.printError(EC.GENERAL, ee);
            }

            throw new FatalException("LW failed", ee);
        }

        // Reset after checking unless it's the final check:
        if (!finalCheck) {
            for (final ILiveChecker iLiveChecker : checker) {
                iLiveChecker.getDiskGraph().makeNodePtrTbl();
            }
        }
        MP.printMessage(EC.TLC_CHECKING_TEMPORAL_PROPS_END, TLC.convertRuntimeToHumanReadable(System.currentTimeMillis() - startTime));

        return EC.NO_ERROR;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#checkTrace(tlc2.tool.StateVec)
     */
    @Override
    public void checkTrace(final ITool tool, final Supplier<StateVec> traceSupplier) throws Exception {
        final StateVec stateTrace = traceSupplier.get();
        // Add the first state to the LiveCheck as the current init state
        addInitState(tool, stateTrace.get(0), stateTrace.get(0).fingerPrint());

        // Add the remaining states...
        final SetOfStates successors = new SetOfStates(stateTrace.size() * 2);

        // For all states except last one add the successor
        // (which is the next state in stateTrace).
        for (int i = 0; i < stateTrace.size() - 1; i++) {
            // Empty out old successors.
            successors.clear();

            // Calculate the current state's fingerprint
            final TLCState tlcState = stateTrace.get(i);
            final long fingerPrint = tlcState.fingerPrint();

            // Add state itself to allow stuttering
            successors.add(tlcState);

            // Add the successor in the trace
            final TLCState successor = stateTrace.get(i + 1);
            successors.add(successor);
            addNextState(tool, tlcState, fingerPrint, successors);
        }

        // Add last state in trace for which *no* successors have been generated
        final TLCState lastState = stateTrace.get(stateTrace.size() - 1);
        addNextState(tool, lastState, lastState.fingerPrint(), new SetOfStates(0));

        // Do *not* re-create the nodePtrTbl when it is thrown away anyway.
        final int result = check0(tool, true);
        if (result != EC.NO_ERROR) {
            throw new LiveException(result);
        }

        // We are done with the current subsequence of the behavior. Reset LiveCheck
        // for the next behavior simulation is going to create.
        reset();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#getMetaDir()
     */
    @Override
    public String getMetaDir() {
        return metadir;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#getOutDegreeStatistics()
     */
    @Override
    public IBucketStatistics getOutDegreeStatistics() {
        return outDegreeGraphStats;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#getChecker(int)
     */
    @Override
    public ILiveChecker getChecker(final int idx) {
        return checker[idx];
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#getNumChecker()
     */
    @Override
    public int getNumChecker() {
        return checker.length;
    }

    /* Close all the files for disk graphs. */
    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#close()
     */
    @Override
    public void close() throws IOException {
        for (final ILiveChecker iLiveChecker : checker) {
            iLiveChecker.close();
        }
    }

    /* Checkpoint. */
    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#beginChkpt()
     */
    @Override
    public synchronized void beginChkpt() throws IOException {
        for (final ILiveChecker iLiveChecker : checker) {
            iLiveChecker.getDiskGraph().beginChkpt();
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#commitChkpt()
     */
    @Override
    public void commitChkpt() throws IOException {
        for (final ILiveChecker iLiveChecker : checker) {
            iLiveChecker.getDiskGraph().commitChkpt();
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#recover()
     */
    @Override
    public void recover() throws IOException {
        for (final ILiveChecker iLiveChecker : checker) {
            MP.printMessage(EC.TLC_AAAAAAA);
            iLiveChecker.getDiskGraph().recover();
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#reset()
     */
    @Override
    public void reset() throws IOException {
        for (final ILiveChecker iLiveChecker : checker) {
            iLiveChecker.getDiskGraph().reset();
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#calculateInDegreeDiskGraphs(tlc2.util.statistics.IBucketStatistics)
     */
    @Override
    public IBucketStatistics calculateInDegreeDiskGraphs(final IBucketStatistics aGraphStats) {
        for (final ILiveChecker iLiveChecker : checker) {
            final AbstractDiskGraph diskGraph = iLiveChecker.getDiskGraph();
            diskGraph.calculateInDegreeDiskGraph(aGraphStats);
        }
        return aGraphStats;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#calculateOutDegreeDiskGraphs(tlc2.util.statistics.IBucketStatistics)
     */
    @Override
    public IBucketStatistics calculateOutDegreeDiskGraphs(final IBucketStatistics aGraphStats) {
        for (final ILiveChecker iLiveChecker : checker) {
            final AbstractDiskGraph diskGraph = iLiveChecker.getDiskGraph();
            diskGraph.calculateOutDegreeDiskGraph(aGraphStats);
        }
        return aGraphStats;
    }

    abstract static class AbstractLiveChecker implements ILiveChecker {

        protected final ILivenessStateWriter writer;

        protected final OrderOfSolution oos;

        public AbstractLiveChecker(final OrderOfSolution oos, final ILivenessStateWriter writer) {
            this.oos = oos;
            this.writer = writer;
        }

        /* (non-Javadoc)
         * @see tlc2.tool.liveness.ILiveChecker#getSolution()
         */
        @Override
        public OrderOfSolution getSolution() {
            return oos;
        }

        /* (non-Javadoc)
         * @see tlc2.tool.liveness.ILiveChecker#close()
         */
        @Override
        public void close() throws IOException {
            if (!ModelChecker.VETO_CLEANUP) {
                this.getDiskGraph().close();
            }
            this.writer.close();
        }
    }

    private class LiveChecker extends AbstractLiveChecker {

        private final DiskGraph dgraph;

        public LiveChecker(final OrderOfSolution oos, final int soln, final IBucketStatistics bucketStatistics, final ILivenessStateWriter writer)
                throws IOException {
            super(oos, writer);
            this.dgraph = new DiskGraph(metadir, soln, bucketStatistics);
        }

        /* (non-Javadoc)
         * @see tlc2.tool.liveness.LiveCheck.ILiveChecker#addInitState(tlc2.tool.TLCState, long)
         */
        @Override
        public void addInitState(final ITool tool, final TLCState state, final long stateFP) {
            dgraph.addInitNode(stateFP, -1);
            writer.writeState(state);
        }

        /* (non-Javadoc)
         * @see tlc2.tool.liveness.ILiveChecker#addNextState(tlc2.tool.TLCState, long, tlc2.util.SetOfStates, tlc2.util.BitSet, boolean[])
         */
        @Override
        public void addNextState(final ITool tool, final TLCState s0, final long fp0,
                                 final SetOfStates nextStates, final BitSet checkActionResults, final boolean[] checkStateResults) throws IOException {
            int cnt = 0;
            // if there is no tableau ...
            final int succCnt = nextStates.size();
            final int alen = oos.getCheckAction().length;
            synchronized (oos) {
                final GraphNode node0 = dgraph.getNode(fp0);
                final int s = node0.succSize();
                node0.setCheckState(checkStateResults);
                final var nextStatesIterator = nextStates.iterator();
                for (int sidx = 0; sidx < succCnt; sidx++) {
                    final TLCState successorState = nextStatesIterator.next();
                    final long successor = successorState.fingerPrint();
                    // Only add the transition if:
                    // a) The successor itself has not been written to disk
                    //    TODO Why is an existing successor ignored?
                    // b) The successor is a new outgoing transition for s0
                    final long ptr1 = dgraph.getPtr(successor);
                    if (ptr1 == -1 || !node0.transExists(successor, -1)) {
                        // Eagerly allocate as many (N) transitions (outgoing arcs)
                        // as we are maximally going to add within the for
                        // loop. This reduces GraphNode's internal and
                        // *performance-wise expensive* System.arraycopy calls
                        // from N invocations to one (best case) or two (worst
                        // case). It has been found empirically (VoteProof) that
                        // the best case is used most of the time (99%).
                        // It should also minimize the work created for Garbage
                        // Collection to clean up even in the worst-case (two invocations)
                        // when the pre-allocated memory has to be freed (see
                        // realign call).
                        // Rather than allocating N memory regions and freeing
                        // N-1 immediately after, it now just has to free a
                        // single one (and only iff we over-allocated).
                        node0.addTransition(successor, -1, checkStateResults.length, alen,
                                checkActionResults, sidx * alen, (succCnt - cnt++));
                    } else {
                        cnt++;
                    }
                    writer.writeState(s0, successorState, checkActionResults, sidx * alen, alen, ptr1 == -1);
                }

                // In simulation mode (see Simulator), it's possible that this
                // method is called multiple times for the same state (s0/fp0)
                // but with changing successors caused by the random successor
                // selection. If the successor is truly new (it has not been
                // added before), the GraphNode instance has to be updated
                // (creating a new record on disk). However, when the successor
                // parameter happens to pass known successors only, there is no
                // point in adding the GraphNode again. It would just waste disk
                // space.
                // The amount of successors is either 0 (no new successor has
                // been added) or used to be less than it is now.
                if ((s == 0 && s == node0.succSize()) || s < node0.succSize()) {
                    node0.realign(); // see node0.addTransition() hint
                    // Add a node for the current state. It gets added *after*
                    // all transitions have been added because addNode
                    // immediately writes the GraphNode to disk including its
                    // transitions.
                    dgraph.addNode(node0);
                } else {
                    // Since the condition is only supposed to evaluate to false
                    // when LiveCheck is used in simulation mode, mainChecker
                    // has to be null.
                    var mainChecker = tool.getMainChecker();
                    Assert.check(mainChecker == null, EC.GENERAL);
                }
            }
        }

        @Override
        public DiskGraph getDiskGraph() {
            return dgraph;
        }
    }

    private class TableauLiveChecker extends AbstractLiveChecker {

        private final TableauDiskGraph dgraph;
        private GraphNode errorGraphNode = null;

        public TableauLiveChecker(final OrderOfSolution oos, final int soln, final IBucketStatistics statistics, final ILivenessStateWriter writer)
                throws IOException {
            super(oos, writer);
            this.dgraph = new TableauDiskGraph(metadir, soln, statistics);
        }

        /* (non-Javadoc)
         * @see tlc2.tool.liveness.LiveChecker#addInitState(tlc2.tool.TLCState, long)
         */
        @Override
        public void addInitState(final ITool tool, final TLCState state, final long stateFP) {
            // (state, tnode) is a root node if tnode is an initial tableau
            // node and tnode is consistent with state.
            final int initCnt = oos.getTableau().getInitCnt();
            for (int i = 0; i < initCnt; i++) {
                final TBGraphNode tnode = oos.getTableau().getNode(i);
                if (tnode.isConsistent(state, tool)) {
                    dgraph.addInitNode(stateFP, tnode.getIndex());
                    dgraph.recordNode(stateFP, tnode.getIndex());
                    writer.writeState(state, tnode);
                }
            }
        }

        /* (non-Javadoc)
         * @see tlc2.tool.liveness.ILiveChecker#addNextState(tlc2.tool.TLCState, long, tlc2.util.SetOfStates, tlc2.util.BitSet, boolean[])
         */
        @Override
        public void addNextState(final ITool tool, final TLCState s0, final long fp0,
                                 final SetOfStates nextStates, final BitSet checkActionResults, final boolean[] checkStateResults) throws Exception {
            int cnt = 0;
            final int succCnt = nextStates.size();

            var mainChecker = tool.getMainChecker();

            //TODO: See regression introduced by moving TBGraphNode#isConsistent
            //      out of the (synchronized) loop below (commit d4908d0).
            //      https://github.com/tlaplus/tlaplus/issues/614

            // Pre-compute the consistency of the successor states for all
            // nodes in the tableau. This is an expensive operation which is
            // also dependent on the amount of nodes in the tableau times
            // the number of successors. This used to be done within the
            // global oos lock which caused huge thread contention. This variant
            // trades speed for additional memory usage (BitSet).
            final TBGraph tableau = oos.getTableau();
            final BitSet consistency = new BitSet(tableau.size() * succCnt);

            for (final TBGraphNode tableauNode : tableau) {

                final var nextStatesIterator = nextStates.iterator();
                for (int sidx = 0; sidx < succCnt; sidx++) {
                    final TLCState s1 = nextStatesIterator.next();
                    if (tableauNode.isConsistent(s1, tool)) {
                        // BitSet is divided into a segment for each
                        // tableau node. Inside each segment, addressing is done
                        // via each state. Use identical addressing below
                        // where the lookup is done.
                        consistency.set((tableauNode.getIndex() * succCnt) + sidx);
                    }
                }
            }

            // At this point only constant time operations are allowed =>
            // Shortly lock the graph.
            //
            // Tests revealed that "synchronized" provides better performance
            // compared to "java.util.concurrent.locks.Lock" even for high
            // thread numbers (up to 32 threads). The actual numbers for EWD840
            // with N=11 and 32 threads were ~75% compared to ~55% thread concurrency.
            synchronized (oos) {

                // Mark the fingerprint of s in s -> t as done. Internally it creates
                // or updates a record in the TableauNodePtrTable. We can safely mark
                // s0/fp0 done even though we release the oos lock, because no other
                // worker will work on s0/fp0 ever again, which is guaranteed by safety-
                // checking.
                final int loc0 = dgraph.setDone(fp0);
                final int[] nodes = dgraph.getNodesByLoc(loc0);
                if (nodes == null) {
                    // There seems to be no case where nodes can end up as null.
                    // setDone(fp0) creates an int[] in dgraph and
                    // getNodesByLoc(loc0) returns it.
                    return;
                }

                final int alen = oos.getCheckAction().length;

                // See node0.addTransition(..) of previous case for what the
                // allocation hint is used for.
                final int allocationHint = ((nodes.length / dgraph.getElemLength()) * succCnt);

                for (int nidx = 2; nidx < nodes.length; nidx += dgraph.getElemLength()) {
                    final int tidx0 = nodes[nidx];
                    final TBGraphNode tnode0 = oos.getTableau().getNode(tidx0);
                    final GraphNode node0 = dgraph.getNode(fp0, tidx0);
                    final int s = node0.succSize();
                    node0.setCheckState(checkStateResults);

                    final var nextStatesIterator = nextStates.iterator();
                    for (int sidx = 0; sidx < succCnt; sidx++) {
                        final TLCState s1 = nextStatesIterator.next();
                        final long successor = s1.fingerPrint();
                        final boolean isDone = dgraph.isDone(successor);
                        for (int k = 0; k < tnode0.nextSize(); k++) {
                            final TBGraphNode tnode1 = tnode0.nextAt(k);
                            // Check if the successor is new
                            final long ptr1 = dgraph.getPtr(successor, tnode1.getIndex());
                            if (consistency.get((tnode1.getIndex() * succCnt) + sidx)
                                    // We cannot infer from successor t being in the fingerprint graph (FG), that it is
                                    // also in the behavior graph (BG):
                                    // a) Worker A might add t to FG. B observes t in the fingerprint graph and adds
                                    // t to BG *incorrectly assuming it is done*.
                                    // b) t in FG does not imply that <<t, tnode>> in BG
                                    // Without a), LiveChecker.addNextState(ITool, TLCState, long, SetOfStates,
                                    // BitSet, boolean[]) could skip checking t \in BG.
                                    // In other words, t \in FG is a necessary but not a sufficient condition...
                                    && (ptr1 == -1 || !node0.transExists(successor, tnode1.getIndex()))) {
                                node0.addTransition(successor, tnode1.getIndex(), checkStateResults.length, alen,
                                        checkActionResults, sidx * alen, allocationHint - cnt);
                                writer.writeState(s0, tnode0, s1, tnode1, checkActionResults, sidx * alen, alen, true);
                                // Record that we have seen <successor,tnode1>. If fp1 is done, we have
                                // to compute the next states for <successor, tnode1>.
                                if (ptr1 == -1) {
                                    dgraph.recordNode(successor, tnode1.getIndex());
                                    if (isDone) {
                                        addNextState(tool, s1, successor, tnode1, oos, dgraph);
                                    }
                                }
                            }
                            // Increment cnt even if addTrasition is not called. After all,
                            // the for loop has completed yet another iteration.
                            cnt++;
                        }
                    }

                    // See same case in LiveChecker#addNextState
                    if ((s == 0 && s == node0.succSize()) || s < node0.succSize()) {
                        node0.realign(); // see node0.addTransition() hint
                        dgraph.addNode(node0);
                    } else {
                        // Since the condition is only supposed to evaluate to false
                        // when LiveCheck is used in simulation mode, mainChecker
                        // has to be null.
                        Assert.check(mainChecker == null, EC.GENERAL);
                    }
                }

                if (errorGraphNode != null) {
                    MP.printError(EC.TLC_TEMPORAL_PROPERTY_VIOLATED);
                    MP.printError(EC.TLC_COUNTER_EXAMPLE);

                    // Lock mainChecker to prevent another TLC Worker from concurrently printing a
                    // (state-graph) safety violation.
                    synchronized (Objects.requireNonNull(mainChecker)) {

                        dgraph.createCache();
                        final LongVec prefix = dgraph.getPath(errorGraphNode.stateFP, errorGraphNode.tindex);
                        dgraph.destroyCache();

                        final int plen = prefix.size();
                        final List<TLCStateInfo> states = new ArrayList<>(plen);

                        // Reconstruct the initial state.
                        long fp = prefix.get(plen - 1);
                        TLCStateInfo sinfo = tool.getState(fp);
                        if (sinfo == null) {
                            throw new EvalException(EC.TLC_FAILED_TO_RECOVER_INIT);
                        }
                        states.add(sinfo);

                        // Reconstruct the path of successor states while dropping
                        // *finite* stuttering.
                        for (int i = plen - 2; i >= 0; i--) {
                            final long curFP = prefix.get(i);
                            if (curFP != fp) {
                                sinfo = tool.getState(curFP, sinfo);
                                states.add(sinfo);
                                fp = curFP;
                            }
                        }

                        for (int i = 0; i < states.size() - 1; i++) {
                            StatePrinter.printInvariantViolationStateTraceState(
                                    tool.getLiveness().evalAlias(states.get(i), states.get(i + 1).state));
                        }
                        // Evaluate alias on the last state that completes the violation of the safety
                        // property.
                        final TLCStateInfo last = states.get(states.size() - 1);
                        StatePrinter.printInvariantViolationStateTraceState(
                                tool.getLiveness().evalAlias(last, last.state));

                        // Stop subsequent state-space exploration.
                        mainChecker.stop();
                        if (states.size() == 1) {
                            mainChecker.setErrState(last.state, null, false,
                                    EC.TLC_INVARIANT_VIOLATED_BEHAVIOR);
                        } else {
                            mainChecker.setErrState(states.get(states.size() - 2).state, last.state, false,
                                    EC.TLC_INVARIANT_VIOLATED_BEHAVIOR);
                        }


                        tool.checkPostConditionWithCounterExample(new CounterExample(states));

                        errorGraphNode = null;
                        throw new InvariantViolatedException();
                    }
                }
            }
        }

        /**
         * This method takes care of the case that a new node <<state, tableau>>
         * in the (state X tableau) graph is generated after the state itself
         * has been done. Done means that the state has been found during safety
         * checking in the state graph already, except that the node <<state,
         * tableau>> not been created.
         * <p>
         * In this case, we will have to generate the state graph successors of
         * the state and create the permutation of all successors with all
         * tableau nodes .
         * <p>
         * Hopefully, this case does not occur very frequently because it
         * generates successor nodes.
         */
        private void addNextState(final ITool tool, final TLCState s, final long fp, final TBGraphNode tnode, final OrderOfSolution oos, final TableauDiskGraph dgraph)
                throws IOException {
            final boolean[] checkStateRes = oos.checkState(tool, s);
            final int slen = checkStateRes.length;
            final int alen = oos.getCheckAction().length;
            final GraphNode node = dgraph.getNode(fp, tnode.getIndex());
            final int numSucc = node.succSize();
            node.setCheckState(checkStateRes);

            // see allocationHint of node.addTransition() invocations below
            int cnt = 0;

            // Add edges induced by s -> s (self-loop) coming from the tableau
            // graph:
            final int nextSize = tnode.nextSize();
            final BitSet checkActionResults = nextSize > 0 ? oos.checkAction(tool, s, s, new BitSet(alen), 0) : null;
            for (int i = 0; i < nextSize; i++) {
                final TBGraphNode tnode1 = tnode.nextAt(i);
                final int tidx1 = tnode1.getIndex();
                final long ptr1 = dgraph.getPtr(fp, tidx1);
                if (tnode1.isConsistent(s, tool)) {
                    if (tnode1.isAccepting() && this.errorGraphNode == null) {
                        // MAK 01/2022:
                        //
                        // If tnode1 is a sink in the tableau graph, i.e., it is accepting and state s
                        // (from the state-graph) is consistent with this tnode1, we know that s is the
                        // final state of a counter-example of a safety property.
                        //
                        // What then has to happen is to reconstruct the path in the behavior graph
                        // (TableauGraph) from some initial node to the GraphNode node (with
                        // <<s.fingerprint, tnode1.getIndex>). However, the GraphNodes of a suffix of
                        // this path might not have been added to the behavior graph yet. Instead, these
                        // GraphNodes have been pushed onto the (Java) call-stack and will only be added
                        // after returning from this method. Thus, we remember/save GraphNode node in
                        // errorGraphNode and preemptively return from behavior graph exploration.
                        //
                        // Once all GraphNodes from the suffix have been added to the behavior graph,
                        // the calling method TableauLiveChecker.addNextState(ITool, TLCState, long,
                        // SetOfStates, BitSet, boolean[]) can reconstruct the path from the
                        // GraphNodes in the behavior graph (TableauGraph#getPath), and print the actual
                        // error-trace by recreating the sequence of states from their fingerprints in
                        // the state graph.
                        this.errorGraphNode = node;
                        return;
                    }
                    if (ptr1 == -1 || !node.transExists(fp, tidx1)) {
                        node.addTransition(fp, tidx1, slen, alen, checkActionResults, 0, (nextSize - cnt));
                        if (ptr1 == -1) {
                            dgraph.recordNode(fp, tnode1.getIndex());
                            addNextState(tool, s, fp, tnode1, oos, dgraph);
                        }
                    }
                }
                cnt++;
            }

            // Add edges induced by s -> s1 (where s1 is a successor of s in the
            // state graph):
            cnt = 0;
            final Action[] actions = tool.getActions();
            for (final Action action : actions) {
                final StateVec nextStates = tool.getNextStates(action, s);
                final int nextCnt = nextStates.size();
                for (final TLCState s1 : nextStates) {
                    if (tool.isInModel(s1) && tool.isInActions(s, s1)) {
                        final long fp1 = s1.fingerPrint();
                        final BitSet checkActionRes = oos.checkAction(tool, s, s1, new BitSet(alen), 0);
                        final boolean isDone = dgraph.isDone(fp1);
                        for (int k = 0; k < tnode.nextSize(); k++) {
                            final TBGraphNode tnode1 = tnode.nextAt(k);
                            final int tidx1 = tnode1.getIndex();
                            final long ptr1 = dgraph.getPtr(fp1, tidx1);
                            final int total = actions.length * nextCnt * tnode.nextSize();
                            if (tnode1.isConsistent(s1, tool) && (ptr1 == -1 || !node.transExists(fp1, tidx1))) {
                                node.addTransition(fp1, tidx1, slen, alen, checkActionRes, 0, (total - cnt));
                                writer.writeState(s, tnode, s1, tnode1, checkActionRes, 0, alen, false, Visualization.DOTTED);
                                // Record that we have seen <fp1, tnode1>. If
                                // fp1 is done, we have to compute the next
                                // states for <fp1, tnode1>.
                                if (ptr1 == -1) {
                                    dgraph.recordNode(fp1, tidx1);
                                    if (isDone) {
                                        addNextState(tool, s1, fp1, tnode1, oos, dgraph);
                                    }
                                }
                            }
                            cnt++;
                        }
                    } else {
                        cnt++;
                    }
                }
            }
            if (numSucc < node.succSize()) {
                node.realign(); // see node.addTransition() hint
                dgraph.addNode(node);
            }
        }

        /* (non-Javadoc)
         * @see tlc2.tool.liveness.LiveCheck.AbstractLiveChecker#getDiskGraph()
         */
        @Override
        public AbstractDiskGraph getDiskGraph() {
            return dgraph;
        }
    }
}
