// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 17 September 2008 at  4:35:32 PST by lamport
//      modified on Thu Jan 10 18:41:04 PST 2002 by yuanyu

package tlc2.tool.liveness;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.StatePrinter;
import tlc2.tool.EvalException;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.util.IdThread;
import tlc2.util.IntStack;
import tlc2.util.LongVec;
import tlc2.util.MemIntQueue;
import tlc2.util.MemIntStack;
import tlc2.util.SynchronousDiskIntStack;
import tlc2.util.statistics.BucketStatistics;
import tlc2.util.statistics.IBucketStatistics;

/**
 * {@link LiveWorker} is doing the heavy lifting of liveness checking:
 * <ul>
 * <li>Searches for strongly connected components (SCC) a.k.a. cycles in the
 * liveness/behavior graph.</li>
 * <li>Checks each SCC if it violates the liveness properties.</li>
 * <li>In case of a violation, reconstructs and prints the error trace.</li>
 * </ul>
 */
public class LiveWorker extends IdThread {

	/**
	 * A marker that is pushed onto the dfsStack during SCC depth-first-search
	 * to marker an explored nodes on the stack.
	 * <p>
	 * A node with a marker is on the comStack.
	 */
	private static final long SCC_MARKER = -42L;

	public static final IBucketStatistics STATS = new BucketStatistics("Histogram SCC sizes", LiveWorker.class
			.getPackage().getName(), "StronglyConnectedComponent sizes");
	
	private static int errFoundByThread = -1;
	private static final Object workerLock = new Object();

	private OrderOfSolution oos = null;
	private AbstractDiskGraph dg = null;
	private PossibleErrorModel pem = null;
	private final ILiveCheck liveCheck;
	private final BlockingQueue<ILiveChecker> queue;
	private final boolean isFinalCheck;
	/**
	 * Total number of LiveWorkers simultaneously checking liveness.
	 */
	private final int numWorkers;

	public LiveWorker(int id, int numWorkers, final ILiveCheck liveCheck, final BlockingQueue<ILiveChecker> queue, final boolean finalCheck) {
		super(id);
		this.numWorkers = numWorkers;
		this.liveCheck = liveCheck;
		this.queue = queue;
		this.isFinalCheck = finalCheck;
		
		// Set the name to something more indicative than "Thread-4711".
		this.setName("TLCLiveWorkerThread-" + String.format("%03d", id));
	}

	/**
	 * Returns true iff an error has already been found.
	 */
	public static boolean hasErrFound() {
		synchronized (workerLock) {
			return (errFoundByThread != -1);
		}
	}

	/**
	 * Returns true iff either an error has not been found or the error is found
	 * by this thread.
	 * <p>
	 * This is used so that only one of the threads which have found an error
	 * prints it.
	 */
	private/* static synchronized */boolean setErrFound() {
		synchronized (workerLock) {
			if (errFoundByThread == -1) {
				errFoundByThread = this.myGetId(); // GetId();
				return true;
			} else if (errFoundByThread == this.myGetId()) { // (* GetId()) {
				return true;
			}
			return false;
		}
	}

	/**
	 * The main routine that computes strongly connected components (SCCs) (see
	 * http://en.wikipedia.org/wiki/Strongly_connected_component), and checks
	 * each of them to see if it contains a counterexample.
	 * <p>
	 * It is Tarjan's SCC algorithm at work:
	 * <p>
	 * The notable differences to the text book algorithm are:
	 * <ul>
	 * <li>It is implemented iteratively (probably to prevent StackOverflows)
	 * </li>
	 * <li>The lowLink number gets pushed onto the DFS stack</li>
	 * <li>If a node is on the DFS stack is determined by checking if it has a
	 * link number assigned</li>
	 * <li>Once an SCC has been found, it is checked immediately for liveness
	 * violations (there is no point it searching all SCCs if the first SCC
	 * found already violates liveness)</li>
	 * <li>Not all states are added to the set of unexplored nodes initially,
	 * but only the model checking init states (all successors are known to be
	 * reachable from the init states).</li>
	 * <li>Liveness is checked periodically during model checking and thus
	 * checkSccs runs on a partial graph. Thus some nodes are marked undone.
	 * Those nodes are skipped by the SCC search.</li>
	 * </ul>
	 * @throws ExecutionException 
	 * @throws InterruptedException 
	 * 
	 * @see http://en.wikipedia.org/wiki/Tarjan'
	 *      s_strongly_connected_components_algorithm
	 * @see http://dx.doi.org/10.1137%2F0201010
	 * 
	 */
	private final void checkSccs() throws IOException, InterruptedException, ExecutionException {
		// Initialize this.dg:
		this.dg.makeNodePtrTbl();
		
		// Initialize nodeQueue with initial states. The initial states stored 
		// separately in the DiskGraph are resolved to their pointer location
		// in the on-disk part of the DiskGraph.
		// The pointer location generally is obviously used to:
		// * Speed up disk lookups in the RandomAccessFile(s) backing up the DiskGraph
		// * Is replaced by the SCC link number the moment the node's successors
		//   are explored during DFS search. At this point the ptr location isn't
		//   needed anymore. The successors have been resolved.
		// 
		// From each node in nodeQueue the SCC search is started down below,
		// which can subsequently add additional nodes into nodeQueue.
		// 
		// Contrary to plain Tarjan, not all vertices are added to the
		// nodeQueue of unexplored states, but only the initial states. Since we
		// know that all non-initial states are reachable from the set of
		// initial states, this is sufficient to start with.
		final LongVec initNodes = this.dg.getInitNodes();
		final int numOfInits = initNodes.size();
		// Allocate space for all initial states, assuming the majority of
		// initial nodes will be done. Multiplied by 5 because of
		// <<long, int, long>> per "record.
		final MemIntQueue nodeQueue = new MemIntQueue(liveCheck.getMetaDir(), "root", (numOfInits / 2) * 5);
		for (int j = 0; j < numOfInits; j += 2) {
			final long state = initNodes.elementAt(j);
			final int tidx = (int) initNodes.elementAt(j + 1);
			final long ptr = this.dg.getLink(state, tidx);
			// Check if the node <<state, tidx>> s is done. A node s is undone
			// if it is an initial state which hasn't been explored yet. This is
			// the case if s has been added via LiveChecker#addInitState but not
			// yet via LiveChecker#addNextState. LiveChecker#addNextState fully
			// explores the given init state s because it has access to s'
			// successors.
			if (ptr >= 0) {
				// Make sure none of the init states has already been assigned a
				// link number. That would indicate a bug in makeNodePtrTbl
				// which is supposed to reset all link numbers to file ptrs.
				assert DiskGraph.isFilePointer(ptr);
				nodeQueue.enqueueLong(state);
				nodeQueue.enqueueInt(tidx);
				nodeQueue.enqueueLong(ptr);
			} else {
				// If this is the final check on the complete graph, no node is
				// allowed to be undone. If it's not the final check, ptr has to
				// be UNDONE (a non-UNDONE negative pointer is probably a bug).
				// isFinalCheck => ptr # UNDONE
				assert !isFinalCheck || ptr != TableauNodePtrTable.UNDONE;
			}
		}

		final int[] eaaction = this.pem.EAAction;
		final int slen = this.oos.getCheckState().length;
		final int alen = this.oos.getCheckAction().length;
		
		// Tarjan's stack
		// Append thread id to name for unique disk files during concurrent SCC search 
		final IntStack dfsStack = getStack(liveCheck.getMetaDir(), "dfs" + this.myGetId());
		
		// comStack is only being added to during the deep first search. It is passed
		// to the checkComponent method while in DFS though. Note that the nodes pushed
		// onto comStack don't necessarily form a strongly connected component (see
		// comment above this.checkComponent(...) below for more details).
		//
		// See tlc2.tool.liveness.LiveWorker.DetailedFormatter.toString(MemIntStack)
		// which is useful during debugging.
		final IntStack comStack = getStack(liveCheck.getMetaDir(), "com" + this.myGetId());

		// Generate the SCCs and check if they contain a "bad" cycle.
		while (nodeQueue.size() > 0) {
			// Pick one of the unexplored nodes as root and start searching the
			// reachable SCCs from it.
			final long state = nodeQueue.dequeueLong();
			final int tidx = nodeQueue.dequeueInt();
			final long loc = nodeQueue.dequeueLong();

			// Reset (remove all elements) the stack. Logically a new SCC search
			// is being started unrelated to the previous one.
			dfsStack.reset();

			// Push the first node onto the DFS stack which makes it the node
			// from which the depth-first-search is being started.
			dfsStack.pushLong(state);
			dfsStack.pushInt(tidx);
			dfsStack.pushLong(loc);
			// Push the smallest possible link number (confusingly called
			// MAX_PTR here but only because file pointers are < MAX_PTR) as the
			// first link number.
			// [0, MAX_PTR) for file pointers
			// [MAX_PTR, MAX_LINK] for links
			dfsStack.pushLong(DiskGraph.MAX_PTR);
			long newLink = DiskGraph.MAX_PTR;

			while (dfsStack.size() >= 7) {
				final long lowLink = dfsStack.popLong();
				final long curLoc = dfsStack.popLong();
				final int curTidx = dfsStack.popInt();
				final long curState = dfsStack.popLong();
				
				// At this point curLoc is still a file pointer (small MAX_PTR)
				// and not yet replaced by a link (MAX_PTR < curLoc < MAX_LINK).
				assert DiskGraph.isFilePointer(curLoc);
				
				// The current node is explored iff curLoc < 0. If it is indeed fully explored,
				// it means it has potentially found an SCC. Thus, check if this is the case
				// for the current GraphNode.
				// A node is fully explored if the nested loop over its
				// successors down below in the else branch has not revealed any
				// unexplored successors.
				if (curLoc == SCC_MARKER) {
					// Check if the current node's link is lowLink which
					// indicates that the nodes on comStack up to <<curState,
					// curTidx>> form an SCC.
					// If curLink # lowLink, continue by pop'ing the next node
					// from dfsStack. It can either be:
					// - unexplored in which case the else branch is taken and
					//   DFS continues.
					// - be an intermediate node of the SCC and thus curLink #
					//   lowLink for it too.
					// - can be the start of the SCC (curLink = lowLink).
					final long curLink = this.dg.getLink(curState, curTidx);
					assert curLink < AbstractDiskGraph.MAX_LINK;
					if (curLink == lowLink) {
						// The states on the comStack from "top" to <<curState,
						// curTidx>> form an SCC, thus check for "bad" cycle.
						//
						// The cycle does not necessarily include all states in
						// comStack. "top" might very well be curState in which
						// case only a single state is checked by
						// checkComponent.
						//
						// The aforementioned case happens regularly when the
						// behaviors to check don't have cycles at all (leaving
						// single node cycles aside for the moment). The DFS
						// followed each behavior from its initial state (see
						// nodeQueue) all the way to the behavior's end state at
						// which point DFS halts. Since DFS cannot continue
						// (there are no successors) it calls checkComponent now
						// with the current comStack and the end state as
						// <<curState, curTidx>> effectively checking the
						// topmost element of comStack. Unless this single state
						// violates any liveness properties, it gets removed
						// from comStack and DFS continues. Iff DFS still cannot
						// continue because the predecessor to endstate
						// (endstate - 1) has no more successors to explore
						// either, it again calls checkComponent for the single
						// element (endstate - 1). This goes on until either the
						// initial state is reached or an intermediate state has
						// unexplored successors with DFS.
						final boolean isOK = this.checkComponent(curState, curTidx, comStack);
						if (!isOK) {
							// Found a "bad" cycle of one to comStack.size()
							// nodes, no point in searching for more SCCs as we
							// are only interested in one counter-example at a
							// time.
							// checkComponent will have printed the
							// counter-example by now.
							return;
						}
					}
					// Replace previous lowLink (plowLink) with the minimum of
					// the current lowLink and plowLink on the stack.
					final long plowLink = dfsStack.popLong();
					dfsStack.pushLong(Math.min(plowLink, lowLink));
					
				// No SCC found yet	
				} else {
					// Assign newLink to curState:
					final long link = this.dg.putLink(curState, curTidx, newLink);
					// link is -1 if newLink has been assigned to pair
					// <<curState, curTidx>>. If the pair had been assigned a
					// link before, the previous link in range [MAX_PTR,
					// MAX_LINK] is returned. If the link is not -1, it means
					// the node has been explored by this DFS search before.
					if (link == -1) {
						// Push curState back onto dfsStack, but make curState
						// explored:
						dfsStack.pushLong(lowLink);
						dfsStack.pushLong(curState);
						dfsStack.pushInt(curTidx);
						// Push a marker onto the stack that, if pop'ed as
						// curLoc above causes branching to enter the true case
						// of the if block.
						dfsStack.pushLong(SCC_MARKER);

						// Add the tuple <<curState, curTidx, curLoc>> to comStack:
						comStack.pushLong(curLoc);
						comStack.pushInt(curTidx);
						comStack.pushLong(curState);
						
						// Look at all the successors of curState:
						final GraphNode gnode = this.dg.getNode(curState, curTidx, curLoc);
						final int succCnt = gnode.succSize();
						long nextLowLink = newLink;
						// DFS moved on to a new node, thus increment the newLink
						// number by 1 for subsequent exploration.
						newLink = newLink + 1;
						for (int i = 0; i < succCnt; i++) {
							final long nextState = gnode.getStateFP(i);
							final int nextTidx = gnode.getTidx(i);
							final long nextLink = this.dg.getLink(nextState, nextTidx);
							// If <<nextState, nextTidx>> node's link is < 0 it
							// means the node isn't "done" yet (see
							// tlc2.tool.liveness.TableauNodePtrTable.UNDONE).
							// A successor node t of gnode is undone if it is:
							// - An initial state which hasn't been explored yet
							// - t has not been added to the liveness disk graph
							//   itself (only as the successor (transition) of
							//   gnode).
							//
							// If it is >= 0, it either is a:
							// - file pointer location
							// - a previously assigned link (>= MAX_PTR)
							//
							// Iff nextLink == MAX_PTR, it means that the
							// <<nextState, nextTidx>> successor node has been
							// processed by checkComponent. The checks below
							// will result in the successor node being skipped.
							//
							// It is possible that <<nextState, nextTidx>> =
							// <<curState, curTid>> due to self loops. This is
							// intended, as checkAction has to be evaluated for
							// self loops too.
							if (nextLink >= 0) {
								// Check if the arc/transition from <<curState,
								// curTidx>> to <<nextState, nextTidx>>
								// satisfies ("P-satisfiable" MP page 422ff)
								// its PEM's EAAction. If it does, 1/3 of the
								// conditions for P-satisfiability are
								// satisfied. Thus it makes sense to check the
								// other 2/3 in checkComponent (AEAction &
								// Fulfilling promises). If the EAAction does
								// not hold, there is no point in checking the
								// other 2/3. All must hold for
								// P-satisfiability.
								//
								// This check is related to the fairness spec.
								// Usually, it evals to true when no or weak
								// fairness have been specified. False on strong
								// fairness.
								if (gnode.getCheckAction(slen, alen, i, eaaction)) {
									// If the node's nextLink still points to
									// disk, it means it has no link assigned
									// yet which is the case if this node gets
									// explored during DFS search the first
									// time. Since it is new, add it to dfsStack
									// to have it explored subsequently by DFS.
									if (DiskGraph.isFilePointer(nextLink)) {
										dfsStack.pushLong(nextState);
										dfsStack.pushInt(nextTidx);
										dfsStack.pushLong(nextLink); // nextLink is logically a ptr/loc here
										// One would expect a (logical) lowLink
										// being pushed (additionally to the
										// ptr/loc in previous line) onto the
										// stack here. However, it is pushed
										// down below after all successors are
										// on the stack and valid for the
										// topmost successor. For the other
										// successors below the topmost, a link
										// number will be assigned subsequently.
									} else {
										// The node has been processed
										// already, thus use the minimum of its link
										// (nextLink) and nextLowLink.
										nextLowLink = Math.min(nextLowLink, nextLink);
									}
								} else {
									// The transition from <<curState, curTidx>>
									// to <<nextState, nextTidx>> is not
									// P-satisfiable and thus does not need to
									// be checkComponent'ed. However, since we
									// only added initial but no intermediate
									// states to nodeQueue above, we have to add
									// <<nextState, nextTidx>> to nodeQueue if
									// it's still unprocessed (indicated by its
									// on disk state). The current path
									// potentially might be the only one by
									// which DFS can reach it.
									if (DiskGraph.isFilePointer(nextLink)) {
									nodeQueue.enqueueLong(nextState);
									nodeQueue.enqueueInt(nextTidx);
									nodeQueue.enqueueLong(nextLink); // nextLink is logically a ptr/loc here
									}
								}
							} else {
								// If this is the final check on the complete
								// graph, no node is allowed to be undone. If
								// it's not the final check, nextLink has to be
								// UNDONE (a non-UNDONE negative nextLink is
								// probably a bug).
								// isFinalCheck => nextLink # UNDONE
								assert !isFinalCheck || nextLink != TableauNodePtrTable.UNDONE;
							}
						}
						// Push the next lowLink onto stack on top of all
						// successors. It is assigned to the topmost 
						// successor only though.
						dfsStack.pushLong(nextLowLink);
					} else {
						// link above wasn't "-1", thus it has to be a valid
						// link in the known interval.
						assert AbstractDiskGraph.MAX_PTR <= link && link <= AbstractDiskGraph.MAX_LINK; 
						// Push the minimum of the two links onto the stack. If
						// link == DiskGraph.MAX_PTR lowLink will always be the
						// minimum (unless this graph has a gigantic amount of
						// SCCs exceeding (MAX_LINK - MAX_PTR).
						dfsStack.pushLong(Math.min(lowLink, link));
					}
				}
			}
		}
		// Make sure all nodes on comStack have been checkComponent()'ed
		assert comStack.size() == 0;
	}

	private IntStack getStack(final String metaDir, final String name) throws IOException {
		// Synchronize all LiveWorker instances to consistently read free
		// memory. This method is only called during initialization of SCC
		// search, thus synchronization should not cause significant thread
		// contention.
		synchronized (LiveWorker.class) {
			// It is unlikely that the stacks will fit into memory if the
			// size of the behavior graph is larger relative to the available
			// memory. Also take the total number of simultaneously running
			// workers into account that have to share the available memory
			// among each other.
			final double freeMemoryInBytes = (Runtime.getRuntime().freeMemory() / (numWorkers * 1d));
			final long graphSizeInBytes = this.dg.getSizeOnDisk();
			final double ratio = graphSizeInBytes / freeMemoryInBytes;
			if (ratio > TLCGlobals.livenessGraphSizeThreshold) {
				// Double SDIS's bufSize/pageSize by how much the graph size
				// overshoots the free memory size, but limit page size to 1gb.
				// Also, don't allocate more than what is available.
				final int capacityInBytes = SynchronousDiskIntStack.BufSize << Math.min((int) ratio, 5);
				if (capacityInBytes < freeMemoryInBytes) {
					return new SynchronousDiskIntStack(metaDir, name, capacityInBytes);
				} else {
					// Use default SDIS which is 32mb of in-memory size
					return new SynchronousDiskIntStack(metaDir, name);
				}
			}
			// If the disk graph as a whole fits into memory, do not use a
			// disk-backed SynchronousDiskIntStack.
			return new MemIntStack(metaDir, name);
		}
	}

	/**
	 * For currentPEM, this method checks if the current SCC satisfies its AEs
	 * and is fulfilling (we know the current SCC satisfies the PEM's EA by the
	 * nested EAaction in checkSccs() above.) If satisfiable, this PEM
	 * contains a counterexample, and this method then calls printErrorTrace to
	 * print an error trace and returns false.
	 * <p>
	 * Speaking in words of Manna & Pnueli (Page 422ff), it checks if ¬&#966;
	 * (which is PEM) is "P-satisfiable" (i.e. is there a computation that
	 * satisfies &#968;). ¬&#966; (called &#968; by MP) is the negation of the
	 * liveness formula &#966; which has to be "P-valid" for the liveness
	 * properties to be valid.
	 * @throws ExecutionException 
	 * @throws InterruptedException 
	 */
	private boolean checkComponent(final long state, final int tidx, final IntStack comStack) throws IOException, InterruptedException, ExecutionException {
		final long comStackSize = comStack.size();
		// There is something to pop and each is a well formed tuple <<fp, tidx, loc>> 
		assert comStackSize >= 5 && comStackSize % 5 == 0; // long + int + long
		
		long state1 = comStack.popLong();
		int tidx1 = comStack.popInt();
		long loc1 = comStack.popLong();

		// Simply return if the component is trivial: It is trivial iff the component
		// has a single node AND this node is *no* stuttering node.
		if (state1 == state && tidx1 == tidx && !isStuttering(state1, tidx1, loc1)) {
			this.dg.setMaxLink(state, tidx);
			return true;
		}

		// Now, we know we are working on a non-trivial component
		// We first put all the nodes in this component in a hashtable. 
		// The nodes in this component do not correspond to
		// all elements on the comStack though. Only the nodes up to
		// the given one are copied to NodePtrTable.
		//
		// The NodePtrTable would ideally be initialized with the number of
		// nodes in the comStack. This is the upper limit of elements going
		// to be kept in com. However, it would destroy NodePtrTable's
		// collision handling. NodePtrTable uses open addressing (see
		// http://en.wikipedia.org/wiki/Open_addressing).
		//
		// Initializing the NTPT with 128 buckets/slows is a significant memory
		// overhead (especially when comStack contains < 10 elements) which
		// regularly results in OutOfMemoryErrors being thrown. To alleviate the
		// problem the key-space of the comStack elements could be checked and
		// the minimum possible collision-free TNPT size be calculated.
		// (Btw. the implementation uses a TNPT in the first place because it is
		// passed on to printTrace iff an error is found. The implementation
		// here could use a simple java.util.Map or HashTable technically.)
		final TableauNodePtrTable com = new TableauNodePtrTable(128);
		while (true) {
			// Add <state1, tidx1> into com:
			com.put(state1, tidx1, loc1);
			this.dg.setMaxLink(state1, tidx1);

			// Get the next node of the component:
			if (state == state1 && tidx == tidx1) {
				break;
			}

			state1 = comStack.popLong();
			tidx1 = comStack.popInt();
			loc1 = comStack.popLong();
		}
		// Just parameter node in com OR com subset of comStack
		assert com.size() <= (comStackSize / 5);

		STATS.addSample(com.size());

		// Check this component:
		final int slen = this.oos.getCheckState().length;
		final int alen = this.oos.getCheckAction().length;
		final int aeslen = this.pem.AEState.length;
		final int aealen = this.pem.AEAction.length;
		final int plen = this.oos.getPromises().length;
		final boolean[] AEStateRes = new boolean[aeslen];
		final boolean[] AEActionRes = new boolean[aealen];
		final boolean[] promiseRes = new boolean[plen];

		// Extract a node from the nodePtrTable "com".
		// Note the upper limit is NodePtrTable#getSize() instead of
		// the more obvious NodePtrTable#size().
		// NodePtrTable internally hashes the elements to buckets
		// and isn't filled start to end. Thus, the code
		// below iterates NodePtrTable front to end skipping null buckets.
		//
		// Note that the nodes are processed in random order (depending on a
		// node's hash in TableauNodePtrTbl) and not in the order given by
		// comStack. This is fine because the all checks have been evaluated
		// eagerly during insertion into the liveness graph long before the
		// SCC search started. Thus, the code here only has to check the 
		// check results which can happen in any order.
		final int tsz = com.getSize();
		for (int ci = 0; ci < tsz; ci++) {
			final int[] nodes = com.getNodesByLoc(ci);
			if (nodes == null) {
				// miss in NotePtrTable (null bucket)
				continue;
			}

			state1 = TableauNodePtrTable.getKey(nodes);
			for (int nidx = 2; nidx < nodes.length; nidx += com.getElemLength()) { // nidx starts with 2 because [0][1] are the long fingerprint state1. 
				tidx1 = TableauNodePtrTable.getTidx(nodes, nidx);
				loc1 = TableauNodePtrTable.getElem(nodes, nidx);

				final GraphNode curNode = this.dg.getNode(state1, tidx1, loc1);

				// Check AEState:
				for (int i = 0; i < aeslen; i++) {
					// Only ever set AEStateRes[i] to true, but never to false
					// once it was true. It only matters if one state in com
					// satisfies PEM's liveness property due to []<>¬p (which is
					// the inversion of <>[]p).
					// 
					// It obviously has to check all nodes in the component
					// (com) if either of them violates AEState unless all
					// elements of AEStateRes are true. From that point onwards,
					// checking further states wouldn't make a difference.
					if (!AEStateRes[i]) {
						int idx = this.pem.AEState[i];
						AEStateRes[i] = curNode.getCheckState(idx);
						// Can stop checking AEStates the moment AEStateRes
						// is completely set to true. However, most of the time
						// aeslen is small and the compiler will probably optimize
						// out.
					}
				}

				// Check AEAction: A TLA+ action represents the relationship
				// between the current node and a successor state. The current
				// node has n successor states. For each pair, see iff the 
				// successor is in the "com" NodePtrTablecheck, check actions
				// and store the results in AEActionRes(ult). Note that the
				// actions have long been checked in advance when the node was
				// added to the graph and the actual state and not just its
				// fingerprint was available. Here, the result is just being
				// looked up.
				final int succCnt = aealen > 0 ? curNode.succSize() : 0; // No point in looping successors if there are no AEActions to check on them.
				for (int i = 0; i < succCnt; i++) {
					final long nextState = curNode.getStateFP(i);
					final int nextTidx = curNode.getTidx(i);
					// For each successor <<nextState, nextTdix>> of curNode's
					// successors check, if it is part of the currently
					// processed SCC (com). Successors, which are not part of
					// the current SCC have obviously no relevance here. After
					// all, we check the SCC.
					if (com.getLoc(nextState, nextTidx) != -1) {
						for (int j = 0; j < aealen; j++) {
							// Only set false to true, but never true to false. 
							if (!AEActionRes[j]) {
								final int idx = this.pem.AEAction[j];
								AEActionRes[j] = curNode.getCheckAction(slen, alen, i, idx);
							}
						}
					}
				}

				// Check that the component is fulfilling. (See MP page 453.)
				// Note that the promises are precomputed and stored in oos.
				for (int i = 0; i < plen; i++) {
					final LNEven promise = this.oos.getPromises()[i];
					final TBPar par = curNode.getTNode(this.oos.getTableau()).getPar();
					if (par.isFulfilling(promise)) {
						promiseRes[i] = true;
					}
				}
			}
		}

		// We find a counterexample if all three conditions are satisfied. If
		// either of the conditions is false, it means the PEM does not hold and
		// thus the liveness properties are not violated by the SCC.
		//
		// All AEState properties, AEActions and promises of PEM must be
		// satisfied. If a single one isn't satisfied, the PEM as a whole isn't
		// P-satisfiable. That's why it returns on the first false. As stated
		// before, EAAction have already been checked if satisfiable.
		// checkComponent is only called if the EA actions are satisfiable.
		//
		// Technically: No error is found if any of the AEStateRes, AEActionRes
		// or promiseRes booleans is false.
		for (int i = 0; i < aeslen; i++) {
			if (!AEStateRes[i]) {
				return true;
			}
		}
		for (int i = 0; i < aealen; i++) {
			if (!AEActionRes[i]) {
				return true;
			}
		}
		for (int i = 0; i < plen; i++) {
			if (!promiseRes[i]) {
				return true;
			}
		}
		// This component must contain a counter-example because all three
		// conditions are satisfied. So, print a counter-example (if this thread
		// is the first one to find a counter-example)!
		if (setErrFound()) {
			this.printTrace(state, tidx, com);
		}
		return false;
	}

	/* Check if the node <state, tidx> stutters. */
	private boolean isStuttering(long state, int tidx, long loc) throws IOException {
		final int slen = this.oos.getCheckState().length;
		final int alen = this.oos.getCheckAction().length;

		// Find the self loop and check its <>[]action
		final GraphNode gnode = this.dg.getNode(state, tidx, loc);
		final int succCnt = gnode.succSize();
		for (int i = 0; i < succCnt; i++) {
			final long nextState = gnode.getStateFP(i);
			final int nextTidx = gnode.getTidx(i);
			if (state == nextState && tidx == nextTidx) {
				return gnode.getCheckAction(slen, alen, i, this.pem.EAAction);
			}
		}
		// <state, tidx> has no self loop, thus cannot stutter
		return false;
	}

	/**
	 * Print out the error state trace by finding a cycle in the given SCC. The
	 * method first generates a "bad" cycle from the current scc, and then
	 * generates a prefix path from some initial state to the "bad" cycle in the
	 * state graph. The prefix path and the "bad" cycle together forms a
	 * counter-example.
	 * <p>
	 * Additionally, the first part can be divided into the two while loops A)
	 * and B). A) re-creates the sub-path of the error trace starting at the
	 * start state of the SCC as given by the parameters and ends when all
	 * states have be accumulated that -combined- violate the liveness
	 * properties. Iff the last state after termination of A) is not equal to
	 * the start state, there is a gap in the cycle. Thus, B) task is to close
	 * the gap.
	 * <p>
	 * 
	 * @see tlatools/test-model/symmetry/ErrorTraceConstructionPhases.png for a
	 *      sketch.
	 * @see tlc2.tool.liveness.ErrorTraceConstructionTest which runs a spec that
	 *      exemplifies the three staged error trace composition
	 *      
	 * @param state
	 *            fingerprint of the state which is the "starting" state of the
	 *            SCC in nodeTbl.
	 * @param tidx
	 *            tableau index pointing to the {@link TBGraph}. Corresponds to
	 *            the state fingerprint. Combined <<state, tidx>> unique
	 *            identify a node in the liveness/behavior graph.
	 * @param nodeTbl
	 *            The current SCC which is known to satisfy the
	 *            {@link PossibleErrorModel} and thus violates the liveness
	 *            properties.
	 * @throws ExecutionException 
	 * @throws InterruptedException 
	 */
	private void printTrace(final long state, final int tidx, final TableauNodePtrTable nodeTbl) throws IOException, InterruptedException, ExecutionException {
//		System.out.println(toDotViz(state, tidx, nodeTbl));

		MP.printError(EC.TLC_TEMPORAL_PROPERTY_VIOLATED);
		MP.printError(EC.TLC_COUNTER_EXAMPLE);
		
		/*
		 * Use a dedicated thread to concurrently search a prefix-path from some
		 * initial node to the state identified by <<state, tidx>>.
		 */
		final ExecutorService executor = Executors.newFixedThreadPool(1);
		final Future<List<TLCStateInfo>> future = executor.submit(new Callable<List<TLCStateInfo>>() {
			/* (non-Javadoc)
			 * @see java.util.concurrent.Callable#call()
			 */
			public List<TLCStateInfo> call() throws Exception {
				// Print the error trace. We first construct the prefix that
				// led to the bad cycle. The nodes on prefix and cycleStack then
				// form the complete counter example.
				int stateNum = 0;
				final LongVec prefix = LiveWorker.this.dg.getPath(state, tidx);
				final int plen = prefix.size();
				final List<TLCStateInfo> states = new ArrayList<TLCStateInfo>(plen);

				// Recover the initial state:
				//TODO This throws an ArrayIndexOutOfBounds if getPath returned a
				// LongVec with just a single element. This happens when the parameter
				// state is one of the init states already.
				long fp = prefix.elementAt(plen - 1);
				TLCStateInfo sinfo = liveCheck.getTool().getState(fp);
				if (sinfo == null) {
					throw new EvalException(EC.TLC_FAILED_TO_RECOVER_INIT);
				}
				sinfo.stateNumber = stateNum++;
				states.add(sinfo);

				// Recover the successor states:
				//TODO Check if path.size has elements
				for (int i = plen - 2; i >= 0; i--) {
					long curFP = prefix.elementAt(i);
					// The prefix might contain duplicates if the path happens to walk
					// along two (or more distinct states which differ in the tableau
					// idx only (same fingerprint). From the counterexample perspective,
					// this is irrelevant iff the identical fingerprints are contiguous.
					// It won't be correct to shorten a path <<fp1,fp2,fp1>> to
					// <<fp2,fp1>> though.
					if (curFP != fp) {
						sinfo = liveCheck.getTool().getState(curFP, sinfo.state);
						if (sinfo == null) {
							throw new EvalException(EC.TLC_FAILED_TO_RECOVER_NEXT);
						}
						sinfo.stateNumber = stateNum++;
						states.add(sinfo);
						fp = curFP;
					}
				}

				// Print the prefix:
				TLCState lastState = null;
				for (int i = 0; i < stateNum; i++) {
					StatePrinter.printState(states.get(i), lastState, i + 1);
					lastState = states.get(i).state;
				}
				return states;
			}
		});

		// First, find a "bad" cycle from the "bad" scc.
		final int slen = this.oos.getCheckState().length;
		final int alen = this.oos.getCheckAction().length;
		// The 3 boolean arrays are used to make sure that the same check result
		// is exactly counted once.
		final boolean[] AEStateRes = new boolean[this.pem.AEState.length];
		final boolean[] AEActionRes = new boolean[this.pem.AEAction.length];
		final boolean[] promiseRes = new boolean[this.oos.getPromises().length];
		// The number/count of all liveness checks. The while loop A) terminates
		// once it has accumulated all states that violate all checks (we know
		// that the states in nodeTbl have to violate the liveness property
		// because we are in printTrace already. checkComponent has already
		// determined that there is a violation).
		int cnt = AEStateRes.length + AEActionRes.length + promiseRes.length;

		final MemIntStack cycleStack = new MemIntStack(liveCheck.getMetaDir(), "cycle");

		// Mark state as visited:
		int[] nodes = nodeTbl.getNodes(state);
		int tloc = nodeTbl.getIdx(nodes, tidx);
		final long ptr = TableauNodePtrTable.getElem(nodes, tloc);
		TableauNodePtrTable.setSeen(nodes, tloc);

		// A)
		//
		// Greedy DFS search for a path satisfying the PossibleErrorModel.
		GraphNode curNode = this.dg.getNode(state, tidx, ptr);
		while (cnt > 0) {
			int cnt0 = cnt;

			_next: while (true) {
				// Check AEState:
				for (int i = 0; i < this.pem.AEState.length; i++) {
					int idx = this.pem.AEState[i];
					if (!AEStateRes[i] && curNode.getCheckState(idx)) {
						AEStateRes[i] = true;
						cnt--;
					}
				}

				// Check if the component is fulfilling. (See MP page 453.)
				// Note that the promises are precomputed and stored in oos.
				for (int i = 0; i < this.oos.getPromises().length; i++) {
					LNEven promise = this.oos.getPromises()[i];
					TBPar par = curNode.getTNode(this.oos.getTableau()).getPar();
					if (!promiseRes[i] && par.isFulfilling(promise)) {
						promiseRes[i] = true;
						cnt--;
					}
				}
				if (cnt <= 0) {
					break;
				}

				// Check AEAction (which is a check of the out-arc of curNode to
				// one of its successors):
				long nextState1 = 0, nextState2 = 0;
				int nextTidx1 = 0, nextTidx2 = 0;
				int tloc1 = -1, tloc2 = -1;
				int[] nodes1 = null, nodes2 = null;
				boolean hasUnvisitedSucc = false;
				int cnt1 = cnt;
				int succCnt = curNode.succSize();
				for (int i = 0; i < succCnt; i++) {
					long nextState = curNode.getStateFP(i);
					int nextTidx = curNode.getTidx(i);
					nodes = nodeTbl.getNodes(nextState);
					if (nodes != null) {
						tloc = nodeTbl.getIdx(nodes, nextTidx);
						if (tloc != -1) {
							// <nextState, nextTidx> is in nodeTbl.
							nextState1 = nextState;
							nextTidx1 = nextTidx;
							tloc1 = tloc;
							nodes1 = nodes;
							for (int j = 0; j < this.pem.AEAction.length; j++) {
								int idx = this.pem.AEAction[j];
								if (!AEActionRes[j] && curNode.getCheckAction(slen, alen, i, idx)) {
									AEActionRes[j] = true;
									cnt--;
								}
							}
						}
					}

					if (cnt < cnt1) {
						// Take curNode -> <nextState, nextTidx>:
						cycleStack.pushInt(curNode.tindex);
						cycleStack.pushLong(curNode.stateFP);
						long nextPtr = TableauNodePtrTable.getPtr(TableauNodePtrTable.getElem(nodes, tloc));
						curNode = this.dg.getNode(nextState, nextTidx, nextPtr);
						nodeTbl.resetElems();
						break _next;
					}

					if (nodes != null && tloc != -1 && !TableauNodePtrTable.isSeen(nodes, tloc)) {
						// <nextState, nextTidx> is an unvisited successor of
						// curNode:
						hasUnvisitedSucc = true;
						nextState2 = nextState;
						nextTidx2 = nextTidx;
						tloc2 = tloc;
						nodes2 = nodes;
					}
				}

				if (cnt < cnt0) {
					// Take curNode -> <nextState1, nextTidx1>:
					cycleStack.pushInt(curNode.tindex);
					cycleStack.pushLong(curNode.stateFP);
					long nextPtr = TableauNodePtrTable.getPtr(TableauNodePtrTable.getElem(nodes1, tloc1));
					curNode = this.dg.getNode(nextState1, nextTidx1, nextPtr);
					nodeTbl.resetElems();
					break;
				}

				// Backtrack if all successors of curNode have been visited
				// and no successor can reduce cnt.
				while (!hasUnvisitedSucc) {
					long curState = cycleStack.popLong();
					int curTidx = cycleStack.popInt();
					long curPtr = TableauNodePtrTable.getPtr(nodeTbl.get(curState, curTidx));
					curNode = this.dg.getNode(curState, curTidx, curPtr);
					succCnt = curNode.succSize();
					for (int i = 0; i < succCnt; i++) {
						nextState2 = curNode.getStateFP(i);
						nextTidx2 = curNode.getTidx(i);
						nodes2 = nodeTbl.getNodes(nextState2);
						if (nodes2 != null) {
							tloc2 = nodeTbl.getIdx(nodes2, nextTidx2);
							if (tloc2 != -1 && !TableauNodePtrTable.isSeen(nodes2, tloc2)) {
								hasUnvisitedSucc = true;
								break;
							}
						}
					}
				}

				// Take curNode -> <nextState2, nextTidx2>. Set nextState2
				// visited.
				cycleStack.pushInt(curNode.tindex);
				cycleStack.pushLong(curNode.stateFP);
				long nextPtr = TableauNodePtrTable.getPtr(TableauNodePtrTable.getElem(nodes2, tloc2));
				curNode = this.dg.getNode(nextState2, nextTidx2, nextPtr);
				TableauNodePtrTable.setSeen(nodes2, tloc2);
			}
		}

		// All the conditions are satisfied. Find a path from curNode
		// to state to form a cycle. Note that:
		// 1. curNode has not been pushed on cycleStack.
		// 2. nodeTbl is trashed after this operation.
		nodeTbl.resetElems();
		final LongVec postfix = new LongVec(16);
		final long startState = curNode.stateFP;

		/*
		 * If the cycle is not closed/completed (complete when startState ==
		 * state), continue from the curNode at which the previous while loop
		 * terminated and follow its successors until the start state shows up.
		 */

		// B)
		//
		// BFS search
		if (startState != state) {
			final MemIntQueue queue = new MemIntQueue(liveCheck.getMetaDir(), null);
			long curState = startState;
			int ploc = -1;
			int curLoc = nodeTbl.getNodesLoc(curState);
			nodes = nodeTbl.getNodesByLoc(curLoc);
			TableauNodePtrTable.setSeen(nodes);

			// B1)
			_done: while (true) {
				tloc = TableauNodePtrTable.startLoc(nodes);
				while (tloc != -1) {
					final int curTidx = TableauNodePtrTable.getTidx(nodes, tloc);
					final long curPtr = TableauNodePtrTable.getPtr(TableauNodePtrTable.getElem(nodes, tloc));
					curNode = this.dg.getNode(curState, curTidx, curPtr);
					final int succCnt = curNode.succSize();

					// for each successor of curNode s, check if s is the
					// destination state.
					for (int j = 0; j < succCnt; j++) {
						final long nextState = curNode.getStateFP(j);

						if (nextState == state) {
							// We have found a path from startState to state,
							// now backtrack the path the outer loop took to get
							// us here and add each state to postfix.
							while (curState != startState) {
								postfix.addElement(curState);
								nodes = nodeTbl.getNodesByLoc(ploc);
								curState = TableauNodePtrTable.getKey(nodes);
								ploc = TableauNodePtrTable.getParent(nodes);
							}
							postfix.addElement(startState);
							break _done;
						}

						// s is not equal to the destination state 'startState'.
						// If s's successors are still unseen, add s to the
						// queue to later explore it as well. Mark it seen
						// to not explore it twice.
						final int[] nodes1 = nodeTbl.getNodes(nextState);
						if (nodes1 != null && !TableauNodePtrTable.isSeen(nodes1)) {
							TableauNodePtrTable.setSeen(nodes1);
							queue.enqueueLong(nextState);
							queue.enqueueInt(curLoc);
						}
					}
					tloc = TableauNodePtrTable.nextLoc(nodes, tloc);
				}
				// Create a parent pointer to later reverse the path in B2)
				TableauNodePtrTable.setParent(nodes, ploc);
				// Dequeue the next unexplored state from the queue.
				curState = queue.dequeueLong();
				ploc = queue.dequeueInt();
				curLoc = nodeTbl.getNodesLoc(curState);
				nodes = nodeTbl.getNodesByLoc(curLoc);
			}
		}
		
		/*
		 * At this point the cycle part of the error trace has been constructed.
		 * cycleStack contains the states from the start state of the SCC up to
		 * the state that violates all liveness properties. postfix contains the
		 * suffix from the violating state back to the start state of the SCC.
		 * Thus, append the reversed cycleStack onto postfix (cycleStack has the
		 * last state at the top). Postfix then contains the minimal path in the
		 * SCC that violates the liveness property.
		 */
		while (cycleStack.size() > 0) {
			// Do not filter successive <<fp,tidx,permId>> here but do it below
			// when the actual states get printed. See Test3.tla for reason why.
			postfix.addElement(cycleStack.popLong());
			cycleStack.popInt(); // ignore tableau idx
		}

		// Wait for the prefix-path to be searched/generated and fully printed.
		final List<TLCStateInfo> states = future.get();

		/*
		 * At this point everything from the initial state up to the start state
		 * of the SCC has been printed. Now, print the states in postfix.
		 */
		TLCStateInfo sinfo = states.get(states.size() - 1);
		TLCState lastState = sinfo.state;
		long fp = lastState.fingerPrint();
		int stateNum = (int) sinfo.stateNumber + 1;
		final int cyclePos = stateNum;
		final long cycleFP = fp;

		for (int i = postfix.size() - 1; i >= 0; i--) {
			final long curFP = postfix.elementAt(i);
			// Only print the state if it differs from its predecessor. We don't
			// want to print an identical state twice. This can happen if the
			// loops A) and B) above added an identical state multiple times
			// into cycleStack/postfix.
			// The reason we don't simply compare the actual states is for
			// efficiency reason. Regenerating the next state might be
			// expensive.
			if (curFP != fp) {
				sinfo = liveCheck.getTool().getState(curFP, sinfo.state);
				if (sinfo == null) {
					throw new EvalException(EC.TLC_FAILED_TO_RECOVER_NEXT);
				}
				StatePrinter.printState(sinfo, lastState, ++stateNum);
				lastState = sinfo.state;
				fp = curFP;
			}
		}

		/* All error trace states have been printed (prefix + cycleStack +
		 * postfix). What is left is to print either the stuttering or the
		 * back-to-cyclePos marker.
		 */ 

		if (fp == cycleFP) {
			StatePrinter.printStutteringState(++stateNum);
		} else {
			sinfo = liveCheck.getTool().getState(cycleFP, sinfo.state);
			if (sinfo == null) {
				throw new EvalException(EC.TLC_FAILED_TO_RECOVER_NEXT);
			}
			// The print stmts below claim there is a cycle, thus assert that
			// there is indeed one. Index-based lookup into states array is
			// reduced by one because cyclePos is human-readable.
			assert states.get(cyclePos - 1).state.equals(sinfo.state);
			StatePrinter.printBackToState(cyclePos);
		}
	}

	/* (non-Javadoc)
	 * @see java.lang.Thread#run()
	 */
	public final void run() {
		try {
			while (true) {
				// Use poll() to get the next checker from the queue or null if
				// there is none. Do *not* block when there are no more checkers
				// available. Nobody is going to add new checkers to the queue.
				final ILiveChecker checker = queue.poll();
				if (checker == null || hasErrFound()) {
					// Another thread has either found an error (violation of a
					// liveness property) OR there is no more work (checker) to
					// be done.
					break;
				}

				this.oos = checker.getSolution();
				this.dg = checker.getDiskGraph();
				this.dg.createCache();
				PossibleErrorModel[] pems = this.oos.getPems();
				for (int i = 0; i < pems.length; i++) {
					if (!hasErrFound()) {
						this.pem = pems[i];
						this.checkSccs();
					}
				}
				this.dg.destroyCache();
				// Record the size of the disk graph at the time its checked. This
				// information is later used to decide if it it makes sense to
				// run the next check on the larger but still *partial* graph.
				this.dg.recordSize();
			}
		} catch (Exception e) {
			MP.printError(EC.GENERAL, "checking liveness", e); // LL changed
			// call 7 April
			// 2012
			// Assert.printStack(e);
			return;
		}
	}

	public String toDotViz(final long state, final int tidx, TableauNodePtrTable tnpt) throws IOException {
		final StringBuffer sb = new StringBuffer(tnpt.size() * 10);
		sb.append("digraph TableauNodePtrTable {\n");
		sb.append("nodesep = 0.7\n");
		sb.append("rankdir=LR;\n"); // Left to right rather than top to bottom

		final int tsz = tnpt.getSize();
		for (int ci = 0; ci < tsz; ci++) {
			final int[] nodes = tnpt.getNodesByLoc(ci);
			if (nodes == null) {
				// miss in TableauNodePtrTable (null bucket)
				continue;
			}

			long state1 = TableauNodePtrTable.getKey(nodes);
			for (int nidx = 2; nidx < nodes.length; nidx += tnpt.getElemLength()) { // nidx starts with 2 because [0][1] are the long fingerprint state1. 
				int tidx1 = TableauNodePtrTable.getTidx(nodes, nidx);
				long loc1 = TableauNodePtrTable.getElem(nodes, nidx);

				final GraphNode curNode = this.dg.getNode(state1, tidx1, loc1);
				sb.append(curNode.toDotViz((state1 == state && tidx1 == tidx), true));
			}
		}
		
		sb.append("}");
		return sb.toString();
	}
	
  	/*
	 * The detailed formatter below can be activated in Eclipse's variable view
	 * by choosing "New detailed formatter" from the MemIntQueue context menu.
	 * Insert "LiveWorker.DetailedFormatter.toString(this);".
	 */
  	public static class DetailedFormatter {
  		public static String toString(final MemIntStack comStack) {
  			final int size = (int) comStack.size();
			final StringBuffer buf = new StringBuffer(size / 5);
  			for (int i = 0; i < comStack.size(); i+=5) {
  				long loc = comStack.peakLong(size - i - 5);
  				int tidx = comStack.peakInt(size - i - 3);
  				long state = comStack.peakLong(size - i - 2);
  				buf.append("state: ");
  				buf.append(state);
  				buf.append(" tidx: ");
  				buf.append(tidx);
  				buf.append(" loc: ");
  				buf.append(loc);
  				buf.append("\n");
  			}
 			return buf.toString();
  		}
  	}

  	/*
	 * The detailed formatter below can be activated in Eclipse's variable view
	 * by choosing "New detailed formatter" from the MemIntQueue context menu.
	 * Insert "LiveWorker.DFSStackDetailedFormatter.toString(this);".
	 * Unfortunately it collides with the comStack DetailedFormatter as both use
	 * the same type MemIntStack. So you have to chose what you want to look at
	 * while debugging.
	 * Note that toString treats pops/pushes of nodes and
	 * states atomically. If called during a node is only partially pushed onto
	 * the stack, the detailed formatter will crash.
	 */
  	public static class DFSStackDetailedFormatter {
  		public static String toString(final MemIntStack dfsStack) {
  			final int size = (int) dfsStack.size();
			final StringBuffer buf = new StringBuffer(size / 7); // approximate the size needed (buf will grow or shrink if needed)
  			int i = 0;
  			for (; i < dfsStack.size();) {
  				// Peak element to see if it's a marker or not
  				final long topElement = dfsStack.peakLong(size - i - 2);
  				if (topElement == SCC_MARKER) {
  					// It is the marker element
  	  				buf.append("node [");
  	  				buf.append(" fp: ");
  	  				buf.append(dfsStack.peakLong(size - i - 5));
  	  				buf.append(" tidx: ");
  	  				buf.append(dfsStack.peakInt(size - i - 3));
  	  				buf.append(" lowLink: ");
  	  				buf.append(dfsStack.peakLong(size - i - 7) - DiskGraph.MAX_PTR);
  	  				buf.append("]\n");
  	  				// Increase i by the number of elements peaked
  	  				i += 7;
  				} else if (DiskGraph.isFilePointer(topElement)) {
  					final long location = topElement;
  	  				buf.append("succ [");
  	  				buf.append(" fp: ");
  	  				buf.append(dfsStack.peakLong(size - i - 5));
  	  				buf.append(" tidx: ");
  	  				buf.append(dfsStack.peakInt(size - i - 3));
  	  				buf.append(" location: ");
  	  				buf.append(location);
  	  				buf.append("]\n");
  	  				// Increase i by the number of elements peaked
  	  				i += 5;
  				} else if (topElement >= DiskGraph.MAX_PTR) {
  					final long pLowLink = topElement - DiskGraph.MAX_PTR;
  	  				buf.append("pLowLink: ");
  	  				buf.append(pLowLink);
  	  				buf.append("\n");
  					i += 2;
  				}
  			}
  			// Assert all elements are used up
  			assert i == size;
 			return buf.toString();
  		}
  	}
}
