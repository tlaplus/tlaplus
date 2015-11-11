// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:44 PST by lamport
//      modified on Thu Jan 10 18:41:04 PST 2002 by yuanyu

package tlc2.tool.liveness;

import java.io.IOException;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.Action;
import tlc2.tool.IStateFunctor;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.BitVector;
import tlc2.util.FP64;
import tlc2.util.SetOfStates;
import tlc2.util.statistics.DummyBucketStatistics;
import tlc2.util.statistics.IBucketStatistics;
import util.Assert;
import util.SimpleFilenameToStream;

public class LiveCheck implements ILiveCheck {

	private final Action[] actions;
	private final Tool myTool;
	private final String metadir;
	private final IBucketStatistics outDegreeGraphStats;
	private final ILiveChecker[] checker;
	
	public LiveCheck(Tool tool, Action[] acts, String mdir, IBucketStatistics bucketStatistics) throws IOException {
		this(tool, acts, Liveness.processLiveness(tool), mdir, bucketStatistics);
	}

	public LiveCheck(Tool tool, Action[] acts, OrderOfSolution[] solutions, String mdir, IBucketStatistics bucketStatistics) throws IOException {
		myTool = tool;
		actions = acts;
		metadir = mdir;
		outDegreeGraphStats = bucketStatistics;
		checker = new ILiveChecker[solutions.length];
		for (int soln = 0; soln < solutions.length; soln++) {
			if (!solutions[soln].hasTableau()) {
				checker[soln] = new LiveChecker(solutions[soln], soln, bucketStatistics);
			} else {
				checker[soln] = new TableauLiveChecker(solutions[soln], soln, bucketStatistics);
			}
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#addInitState(tlc2.tool.TLCState, long)
	 */
	public void addInitState(TLCState state, long stateFP) {
		for (int i = 0; i < checker.length; i++) {
			checker[i].addInitState(state, stateFP);
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#addNextState(tlc2.tool.TLCState, long, tlc2.util.SetOfStates)
	 */
	public void addNextState(TLCState s0, long fp0, SetOfStates nextStates) throws IOException {
		for (int i = 0; i < checker.length; i++) {
			final ILiveChecker check = checker[i];
			final OrderOfSolution oos = check.getSolution();
			final int alen = oos.getCheckAction().length;

			// Check the actions *before* the solution lock is acquired. This
			// increase concurrency as the lock on the OrderOfSolution is pretty
			// coarse grained (it essentially means we lock the complete
			// behavior graph (DiskGraph) just to add a single node). The
			// drawback is obviously, that we create a short-lived BitVector
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
			final BitVector checkActionResults = new BitVector(alen * nextStates.size());
			for (int sidx = 0; sidx < nextStates.size(); sidx++) {
				final TLCState s1 = nextStates.next();
				oos.checkAction(s0, s1, checkActionResults, alen * sidx);
			}
			nextStates.resetNext();
			check.addNextState(s0, fp0, nextStates, checkActionResults, oos.checkState(s0));
			
			// Write the content of the current graph to a file in GraphViz
			// format. Useful when debugging!
//			check.getDiskGraph().writeDotViz(oos.getCheckState().length, alen, new java.io.File(
//					metadir + java.io.File.separator + "dgraph_" + i + "_" + System.currentTimeMillis() + ".dot"));
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#doLiveCheck()
	 */
	public boolean doLiveCheck() {
		for (int i = 0; i < checker.length; i++) {
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
			final AbstractDiskGraph diskGraph = checker[i].getDiskGraph();
			final long sizeAtLastCheck = diskGraph.getSizeAtLastCheck();
			final long sizeCurrently = diskGraph.size();
			final double delta = (sizeCurrently - sizeAtLastCheck) / (sizeAtLastCheck * 1.d);
			if (delta > TLCGlobals.livenessThreshold) {
				return true;
			}
		}
		return false;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#check(boolean)
	 */
	public boolean check(boolean forceCheck) throws Exception {
		if (forceCheck) {
			return check0(false);
		}
		for (int i = 0; i < checker.length; i++) {
			// see note in doLiveCheck() above!
			final AbstractDiskGraph diskGraph = checker[i].getDiskGraph();
			final long sizeAtLastCheck = diskGraph.getSizeAtLastCheck();
			final long sizeCurrently = diskGraph.size();
			final double delta = (sizeCurrently - sizeAtLastCheck) / (sizeAtLastCheck * 1.d);
			if (delta > TLCGlobals.livenessThreshold) {
				return check0(false);
			}
		}
		return true;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#finalCheck()
	 */
	public boolean finalCheck() throws InterruptedException, IOException {
		// Do *not* re-create the nodePtrTable after the check which takes a
		// while for larger disk graphs.
		return check0(true);
	}
	
	/**
	 * @param finalCheck
	 *            If the internal nodePtrTbl should be restored for a subsequent
	 *            liveness check. If this is the final/last check, it's pointless
	 *            to re-create the nodePtrTable.
	 */
	protected boolean check0(final boolean finalCheck) throws InterruptedException, IOException {
		final long startTime = System.currentTimeMillis();
		
		// Sum up the number of nodes in all disk graphs to indicate the amount
		// of work to be done by liveness checking.
		long sum = 0L;
		for (int i = 0; i < checker.length; i++) {
			sum += checker[i].getDiskGraph().size();
		}
		MP.printMessage(EC.TLC_CHECKING_TEMPORAL_PROPS, new String[] { finalCheck ? "complete" : "current",
				Long.toString(sum), checker.length == 1 ? "" : checker.length + " branches of " });

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
		final BlockingQueue<ILiveChecker> queue = new ArrayBlockingQueue<ILiveChecker>(checker.length);
		queue.addAll(Arrays.asList(checker));

		int slen = checker.length;
		int wNum = Math.min(slen, TLCGlobals.getNumWorkers());

		if (wNum == 1) {
			LiveWorker worker = new LiveWorker(0, 1, this, queue, finalCheck);
			worker.run();
		} else {
			final LiveWorker[] workers = new LiveWorker[wNum];
			for (int i = 0; i < wNum; i++) {
				workers[i] = new LiveWorker(i, wNum, this, queue, finalCheck);
				workers[i].start();
			}
			for (int i = 0; i < wNum; i++) {
				workers[i].join();
			}
		}

		if (LiveWorker.hasErrFound()) {
			MP.printMessage(EC.TLC_CHECKING_TEMPORAL_PROPS_END, TLC.convertRuntimeToHumanReadable(System.currentTimeMillis() - startTime));
			return false;
		}
		
		// Reset after checking unless it's the final check:
		if (finalCheck == false) {
			for (int i = 0; i < checker.length; i++) {
				checker[i].getDiskGraph().makeNodePtrTbl();
			}
		}
		MP.printMessage(EC.TLC_CHECKING_TEMPORAL_PROPS_END, TLC.convertRuntimeToHumanReadable(System.currentTimeMillis() - startTime));
		
		return true;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#checkTrace(tlc2.tool.StateVec)
	 */
	public void checkTrace(final StateVec stateTrace) throws InterruptedException, IOException {
		// Add the first state to the LiveCheck as the current init state
		addInitState(stateTrace.elementAt(0), stateTrace.elementAt(0).fingerPrint());
		
		// Add the remaining states...
		final SetOfStates successors = new SetOfStates(stateTrace.size() * 2);

		// For all states except last one add the successor
		// (which is the next state in stateTrace).
		for (int i = 0; i < stateTrace.size() - 1; i++) {
			// Empty out old successors.
			successors.clear();
			
			// Calculate the current state's fingerprint
			final TLCState tlcState = stateTrace.elementAt(i);
			final long fingerPrint = tlcState.fingerPrint();

			// Add state itself to allow stuttering
			successors.put(tlcState);
			
			// Add the successor in the trace
			final TLCState successor = stateTrace.elementAt(i + 1);
			successors.put(successor);
			addNextState(tlcState, fingerPrint, successors);
		}
		
		// Add last state in trace for which *no* successors have been generated
		final TLCState lastState = stateTrace.elementAt(stateTrace.size() - 1);
		addNextState(lastState, lastState.fingerPrint(), new SetOfStates(0));
		
		// Do *not* re-create the nodePtrTbl when it is thrown away anyway.
		if (!check0(true)) {
			throw new LiveException();
		}
		
		// We are done with the current subsequence of the behavior. Reset LiveCheck
		// for the next behavior simulation is going to create.
		reset();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#getMetaDir()
	 */
	public String getMetaDir() {
		return metadir;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#getTool()
	 */
	public Tool getTool() {
		return myTool;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#getOutDegreeStatistics()
	 */
	public IBucketStatistics getOutDegreeStatistics() {
		return outDegreeGraphStats;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#getChecker(int)
	 */
	public ILiveChecker getChecker(final int idx) {
		return checker[idx];
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#getNumChecker()
	 */
	public int getNumChecker() {
		return checker.length;
	}

	/* Close all the files for disk graphs. */
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#close()
	 */
	public void close() throws IOException {
		for (int i = 0; i < checker.length; i++) {
			checker[i].getDiskGraph().close();
		}
	}

	/* Checkpoint. */
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#beginChkpt()
	 */
	public synchronized void beginChkpt() throws IOException {
		for (int i = 0; i < checker.length; i++) {
			checker[i].getDiskGraph().beginChkpt();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#commitChkpt()
	 */
	public void commitChkpt() throws IOException {
		for (int i = 0; i < checker.length; i++) {
			checker[i].getDiskGraph().commitChkpt();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#recover()
	 */
	public void recover() throws IOException {
		for (int i = 0; i < checker.length; i++) {
			MP.printMessage(EC.TLC_AAAAAAA);
			checker[i].getDiskGraph().recover();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#reset()
	 */
	public void reset() throws IOException {
		for (int i = 0; i < checker.length; i++) {
			checker[i].getDiskGraph().reset();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#calculateInDegreeDiskGraphs(tlc2.util.statistics.IBucketStatistics)
	 */
	public IBucketStatistics calculateInDegreeDiskGraphs(final IBucketStatistics aGraphStats) throws IOException {
		for (int i = 0; i < checker.length; i++) {
			final AbstractDiskGraph diskGraph = checker[i].getDiskGraph();
			diskGraph.calculateInDegreeDiskGraph(aGraphStats);
		}
		return aGraphStats;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#calculateOutDegreeDiskGraphs(tlc2.util.statistics.IBucketStatistics)
	 */
	public IBucketStatistics calculateOutDegreeDiskGraphs(final IBucketStatistics aGraphStats) throws IOException {
		for (int i = 0; i < checker.length; i++) {
			final AbstractDiskGraph diskGraph = checker[i].getDiskGraph();
			diskGraph.calculateOutDegreeDiskGraph(aGraphStats);
		}
		return aGraphStats;
	}
	
	static abstract class AbstractLiveChecker implements ILiveChecker {

		protected final OrderOfSolution oos;

		public AbstractLiveChecker(OrderOfSolution oos) {
			this.oos = oos;
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.liveness.ILiveChecker#getSolution()
		 */
		public OrderOfSolution getSolution() {
			return oos;
		}
	}
	
	private class LiveChecker extends AbstractLiveChecker {

		private final DiskGraph dgraph;

		public LiveChecker(OrderOfSolution oos, int soln, IBucketStatistics bucketStatistics)
			throws IOException {
			super(oos);
			this.dgraph = new DiskGraph(metadir, soln, bucketStatistics);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.liveness.LiveCheck.ILiveChecker#addInitState(tlc2.tool.TLCState, long)
		 */
		public void addInitState(TLCState state, long stateFP) {
			dgraph.addInitNode(stateFP, -1);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.liveness.ILiveChecker#addNextState(tlc2.tool.TLCState, long, tlc2.util.SetOfStates, tlc2.util.BitVector, boolean[])
		 */
		public void addNextState(final TLCState s0, final long fp0, final SetOfStates nextStates,
				final BitVector checkActionResults, final boolean[] checkStateResults) throws IOException {
			int cnt = 0;
			// if there is no tableau ...
			final int succCnt = nextStates.size();
			final int alen = oos.getCheckAction().length;
			synchronized (oos) {
				final GraphNode node0 = dgraph.getNode(fp0);
				final int s = node0.succSize();
				node0.setCheckState(checkStateResults);
				for (int sidx = 0; sidx < succCnt; sidx++) {
					final long successor = nextStates.next().fingerPrint();
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
				}
				nextStates.resetNext();
				// In simulation mode (see Simulator), it's possible that this
				// method is called multiple times for the same state (s0/fp0)
				// but with changing successors caused by the random successor
				// selection. If the successor is truly new (it has not been
				// added before), the GraphNode instance has to be updated
				// (creating a new record on disk). However, when the the
				// successor parameter happens to pass known successors, there
				// is no point in adding the GraphNode again. It is assumed that
				// it wouldn't invalidate the result, but it wastes disk space.
				if (s < node0.succSize()) {
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
					Assert.check(TLCGlobals.mainChecker == null, EC.GENERAL);
				}
			}
		}

		public DiskGraph getDiskGraph() {
			return dgraph;
		}
	}

	private class TableauLiveChecker extends AbstractLiveChecker {

		private final TableauDiskGraph dgraph;

		public TableauLiveChecker(OrderOfSolution oos, int soln, IBucketStatistics statistics)
				throws IOException {
			super(oos);
			this.dgraph = new TableauDiskGraph(metadir, soln, statistics);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.liveness.LiveChecker#addInitState(tlc2.tool.TLCState, long)
		 */
		public void addInitState(final TLCState state, final long stateFP) {
			// (state, tnode) is a root node if tnode is an initial tableau
			// node and tnode is consistent with state.
			int initCnt = oos.getTableau().getInitCnt();
			for (int i = 0; i < initCnt; i++) {
				TBGraphNode tnode = oos.getTableau().getNode(i);
				if (tnode.isConsistent(state, myTool)) {
					dgraph.addInitNode(stateFP, tnode.getIndex());
					dgraph.recordNode(stateFP, tnode.getIndex());
				}
			}
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.liveness.ILiveChecker#addNextState(tlc2.tool.TLCState, long, tlc2.util.SetOfStates, tlc2.util.BitVector, boolean[])
		 */
		public void addNextState(final TLCState s0, final long fp0, final SetOfStates nextStates,
				final BitVector checkActionResults, final boolean[] checkStateResults) throws IOException {
			int cnt = 0;
			final int succCnt = nextStates.size();
			
			// Pre-compute the consistency of the successor states for all
			// nodes in the tableau. This is an expensive operation which is
			// also dependent on the amount of nodes in the tableau times
			// the number of successors. This used to be done within the
			// global oos lock which caused huge thread contention. This variant
			// trades speed for additional memory usage (BitVector).
			final TBGraph tableau = oos.getTableau();
			final BitVector consistency = new BitVector(tableau.size() * succCnt);
			@SuppressWarnings("unchecked")
			final Enumeration<TBGraphNode> elements = tableau.elements();
			while(elements.hasMoreElements()) {
				final TBGraphNode tableauNode = elements.nextElement();
				for (int sidx = 0; sidx < succCnt; sidx++) {
					final TLCState s1 = nextStates.next();
					if(tableauNode.isConsistent(s1, myTool)) {
						// BitVector is divided into a segment for each
						// tableau node. Inside each segment, addressing is done
						// via each state. Use identical addressing below
						// where the lookup is done (plus 1 accounts for
						// zero-based addressing).
						consistency.set((tableauNode.getIndex() * succCnt) + sidx);
					}
				}
				nextStates.resetNext();
			}
			
			// At this point only constant time operations are allowed =>
			// Shortly lock the graph.
			//
			// Tests revealed that "synchronized" provides better performance
			// compared to "java.util.concurrent.locks.Lock" even for high 
			// thread numbers (up to 32 threads). The actual numbers for EWD840
			// with N=11 and 32 threads were ~75% compared to ~55% thread concurrency.
			synchronized (oos) {

				// Mark the current fingerprint as done. Internally it creates
				// or updates a record in the TableauNodePtrTable.
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
					for (int sidx = 0; sidx < succCnt; sidx++) {
						final TLCState s1 = nextStates.next();
						final long successor = s1.fingerPrint();
						final boolean isDone = dgraph.isDone(successor);
						for (int k = 0; k < tnode0.nextSize(); k++) {
							final TBGraphNode tnode1 = tnode0.nextAt(k);
							// Check if the successor is new
							final long ptr1 = dgraph.getPtr(successor, tnode1.getIndex());
							if (consistency.get((tnode1.getIndex() * succCnt) + sidx)
									&& (ptr1 == -1 || !node0.transExists(successor, tnode1.getIndex()))) {
								node0.addTransition(successor, tnode1.getIndex(), checkStateResults.length, alen,
										checkActionResults, sidx * alen, allocationHint - cnt);
								// Record that we have seen <fp1,
								// tnode1>. If fp1 is done, we have
								// to compute the next states for <fp1,
								// tnode1>.
								if (ptr1 == -1) {
									dgraph.recordNode(successor, tnode1.getIndex());
									if (isDone) {
										addNextState(s1, successor, tnode1, oos, dgraph);
									}
								}
							}
							// Increment cnt even if addTrasition is not called. After all, 
							// the for loop has completed yet another iteration.
							cnt++;
						}
					}
					nextStates.resetNext();
					// See same case in LiveChecker#addNextState
					if (s < node0.succSize()) {
						node0.realign(); // see node0.addTransition() hint
						dgraph.addNode(node0);
					} else {
						// Since the condition is only supposed to evaluate to false
						// when LiveCheck is used in simulation mode, mainChecker
						// has to be null.
						Assert.check(TLCGlobals.mainChecker == null, EC.GENERAL);
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
		private void addNextState(final TLCState s, final long fp, final TBGraphNode tnode, final OrderOfSolution oos, final TableauDiskGraph dgraph)
				throws IOException {
			final boolean[] checkStateRes = oos.checkState(s);
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
			final BitVector checkActionResults = nextSize > 0 ? oos.checkAction(s, s, new BitVector(alen), 0) : null;
			for (int i = 0; i < nextSize; i++) {
				final TBGraphNode tnode1 = tnode.nextAt(i);
				final int tidx1 = tnode1.getIndex();
				final long ptr1 = dgraph.getPtr(fp, tidx1);
				if (tnode1.isConsistent(s, myTool) && (ptr1 == -1 || !node.transExists(fp, tidx1))) {
					node.addTransition(fp, tidx1, slen, alen, checkActionResults, 0, (nextSize - cnt));
					if (ptr1 == -1) {
						dgraph.recordNode(fp, tnode1.getIndex());
						addNextState(s, fp, tnode1, oos, dgraph);
					}
				}
				cnt++;
			}

			// Add edges induced by s -> s1 (where s1 is a successor of s in the
			// state graph):
			cnt = 0;
			for (int i = 0; i < actions.length; i++) {
				final StateVec nextStates = myTool.getNextStates(actions[i], s);
				final int nextCnt = nextStates.size();
				for (int j = 0; j < nextCnt; j++) {
					final TLCState s1 = nextStates.elementAt(j);
					if (myTool.isInModel(s1) && myTool.isInActions(s, s1)) {
						final long fp1 = s1.fingerPrint();
						final BitVector checkActionRes = oos.checkAction(s, s1, new BitVector(alen), 0);
						boolean isDone = dgraph.isDone(fp1);
						for (int k = 0; k < tnode.nextSize(); k++) {
							final TBGraphNode tnode1 = tnode.nextAt(k);
							final int tidx1 = tnode1.getIndex();
							long ptr1 = dgraph.getPtr(fp1, tidx1);
							final int total = actions.length * nextCnt * tnode.nextSize();
							if (tnode1.isConsistent(s1, myTool) && (ptr1 == -1 || !node.transExists(fp1, tidx1))) {
								node.addTransition(fp1, tidx1, slen, alen, checkActionRes, 0, (total - cnt));
								// Record that we have seen <fp1, tnode1>. If
								// fp1 is done, we have to compute the next
								// states for <fp1, tnode1>.
								if (ptr1 == -1) {
									dgraph.recordNode(fp1, tidx1);
									if (isDone) {
										addNextState(s1, fp1, tnode1, oos, dgraph);
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
		public AbstractDiskGraph getDiskGraph() {
			return dgraph;
		}
	}
	
	// Intended to be used in unit tests only!!! This is not part of the API!!!
	static class TestHelper {
		
		/*
		 * - EWD840 (with tableau) spec with N = 11 and maxSetSize = 9.000.000 => 12GB nodes file, 46.141.438 distinct states
		 * - EWD840 (with tableau) spec with N = 12 and maxSetSize = 9.000.000 => 56GB, 201.334.782 dist. states 
		 */
		
		// The Eclipse Launch configuration has to set the working directory
		// (Arguments tab) to the parent directory of the folder containing the
		// nodes_* and ptrs_* files. The parent folder has to contain the spec
		// and config file both named "MC".
		// metadir is the the name of the folder with the nodes_* and ptrs_*
		// relative to the parent directory. The directory does *not* need to contain the
		// backing file of the fingerprint set or the state queue files.
		public static ILiveCheck recreateFromDisk(final String path) throws Exception {
			// Don't know with which Polynomial the FP64 has been initialized, but
			// the default is 0.
			FP64.Init(0);
			
			// Most models won't need this, but let's increase this anyway.
			TLCGlobals.setBound = 9000000;

			// Re-create the tool to do the init states down below (LiveCheck#init
			// doesn't really need tool).
	        final Tool tool = new Tool("", "MC", "MC", new SimpleFilenameToStream());
	        tool.init(true, null);
	        
			// Initialize tool's actions explicitly. LiveCheck#printTrace is
			// going to access the actions and fails with a NPE unless
			// initialized.
	        tool.getActions();
	        
			final ILiveCheck liveCheck = new LiveCheck(tool, null, path, new DummyBucketStatistics());
			
			// Calling recover requires a .chkpt file to be able to re-create the
			// internal data structures to continue with model checking. However, we
			// only want to execute liveness checks on the current static disk
			// graph. Thus, we don't need the .chkpt file.
			//recover();
			
			// After recovery, one has to redo the init states
			tool.getInitStates(new IStateFunctor() {
				/* (non-Javadoc)
				 * @see tlc2.tool.IStateFunctor#addElement(tlc2.tool.TLCState)
				 */
				public Object addElement(TLCState state) {
					liveCheck.addInitState(state, state.fingerPrint());
					return true;
				}
			});
			
			return liveCheck; 
		}
	}
}
