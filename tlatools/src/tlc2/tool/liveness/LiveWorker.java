// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 17 September 2008 at  4:35:32 PST by lamport
//      modified on Thu Jan 10 18:41:04 PST 2002 by yuanyu

package tlc2.tool.liveness;

import java.io.IOException;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.StatePrinter;
import tlc2.tool.EvalException;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.util.IdThread;
import tlc2.util.LongVec;
import tlc2.util.MemIntQueue;
import tlc2.util.MemIntStack;
import tlc2.util.statistics.BucketStatistics;
import tlc2.util.statistics.IBucketStatistics;

public class LiveWorker extends IdThread {

	public static final IBucketStatistics STATS = new BucketStatistics("Histogram SCC sizes", LiveWorker.class
			.getPackage().getName(), "StronglyConnectedComponent sizes");
	
	static int nextOOS = 0;
	private static int errFoundByThread = -1;
	private static Object workerLock = new Object();

	private OrderOfSolution oos = null;
	private AbstractDiskGraph dg = null;
	private PossibleErrorModel pem = null;
	private final ILiveCheck liveCheck;

	public LiveWorker(int id, final ILiveCheck liveCheck) {
		super(id);
		this.liveCheck = liveCheck;
	}

	public int getNextOOS() {
		synchronized (LiveWorker.class) {
			if (nextOOS < liveCheck.getNumChecker()) {
				return nextOOS++;
			}
			return -1;
		}
	}

	// Returns true iff an error has already found.
	public static boolean hasErrFound() {
		synchronized (workerLock) {
			return (errFoundByThread != -1);
		}
	}

	/**
	 * Returns true iff either an error has not found or the error is found by
	 * this thread.
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
	 * It seems to be using the Path-based strong component algorithm
	 * (http://en.wikipedia.org/wiki/Path-based_strong_component_algorithm).
	 * This assumption however is incorrect! The second stack is not related to
	 * the SCC algorithm. Thus, it is Tarjan's SCC algorithm at work
	 * (http://en.wikipedia.org/wiki/Tarjan's_strongly_connected_components_algorithm).
	 */
	private final void checkSccs() throws IOException {
		// Initialize this.dg:
		this.dg.makeNodePtrTbl();
		
		// Initialize nodeQueue with initial states. The initial states stored 
		// separately in the DiskGraph are resolved to their pointer location
		// in the on-disk part of the DiskGraph.
		// The pointer location is obviously used to:
		// * Speed up disk lookups in the RandomAccessFile(s) backing up the DiskGraph
		// * Seems to serve as a marker for when a node during SCCs is fully explored //VERIFY assumption!
		// 
		final MemIntQueue nodeQueue = new MemIntQueue(liveCheck.getMetaDir(), "root");
		final LongVec initNodes = this.dg.getInitNodes();
		final int numOfInits = initNodes.size();
		for (int j = 0; j < numOfInits; j += 2) {
			final long state = initNodes.elementAt(j);
			final int tidx = (int) initNodes.elementAt(j + 1);
			final long ptr = this.dg.getLink(state, tidx);
			if (ptr >= 0) { //QUESTION When is a ptr < 0?
				nodeQueue.enqueueLong(state);
				nodeQueue.enqueueInt(tidx);
				nodeQueue.enqueueLong(ptr);
			}
		}

		final int[] eaaction = this.pem.EAAction;
		final int slen = this.oos.getCheckState().length;
		final int alen = this.oos.getCheckAction().length;
		
		// Tarjan's stack
		final MemIntStack dfsStack = new MemIntStack(liveCheck.getMetaDir(), "dfs");
		
		// comStack is only being added to during the deep first search. It is passed
		// to the checkComponent method while in DFS though.
		//
		// An Eclipse detailed formatter:
		// StringBuffer buf = new StringBuffer(this.size);
		// for (int i = 1; i < this.size; i+=5) {
		// 	buf.append("state: ");
		// 	buf.append(peakLong(size - i));
		// 	buf.append("\n");
		// 	buf.append(" Tableaux idx: ");
		// 	buf.append(peakInt(size - i - 2));
		// 	buf.append("\n");
		// 	buf.append(" ptr loc: ");
		// 	buf.append(peakLong(size - i - 3));
		// 	buf.append("\n");
		// }
		// return buf.toString();
		//
		final MemIntStack comStack = new MemIntStack(liveCheck.getMetaDir(), "com");

		// Generate the SCCs and check if they contain any "bad" cycle.
		while (nodeQueue.length() > 0) {
			final long state = nodeQueue.dequeueLong();
			final int tidx = nodeQueue.dequeueInt();
			final long loc = nodeQueue.dequeueLong();

			// Start computing SCCs with <state, tidx> as the root node:
			dfsStack.reset();

			dfsStack.pushLong(state);
			dfsStack.pushInt(tidx);
			dfsStack.pushLong(loc);
			dfsStack.pushLong(DiskGraph.MAX_PTR);
			long newLink = DiskGraph.MAX_PTR;

			while (dfsStack.size() > 2) {
				long lowLink = dfsStack.popLong();
				final long curLoc = dfsStack.popLong();
				final int curTidx = dfsStack.popInt();
				final long curState = dfsStack.popLong();
				
				
				// The current node is explored iff curLoc < 0. If it is indeed fully explored,
				// it means it has potentially found an SCC. Thus, check if this is the case
				// for the current GraphNode.
				if (curLoc < 0) {
					final long curLink = this.dg.getLink(curState, curTidx);
					if (curLink == lowLink) {
						// The states on the comStack from top to curState form
						// a SCC.
						// Check for "bad" cycle.
						final boolean isOK = this.checkComponent(curState, curTidx, comStack);
						if (!isOK) {
							// Found a "bad" cycle, no point in searching for more SCCs. 
							return;
						}
					}
					long plowLink = dfsStack.popLong();
					if (lowLink < plowLink) {
						plowLink = lowLink;
					}
					dfsStack.pushLong(plowLink);
					
				// No SCC found yet	
				} else {
					// Assign newLink to curState:
					final long link = this.dg.putLink(curState, curTidx, newLink);
					if (link == -1) {
						// Push curState back onto dfsStack, but make curState
						// explored:
						dfsStack.pushLong(lowLink);
						dfsStack.pushLong(curState);
						dfsStack.pushInt(curTidx);
						dfsStack.pushLong(-1);

						// Add curState to comStack:
						comStack.pushLong(curLoc);
						comStack.pushInt(curTidx);
						comStack.pushLong(curState);
						
						// Look at all the successors of curState:
						final GraphNode gnode = this.dg.getNode(curState, curTidx, curLoc);
						final int succCnt = gnode.succSize();
						long nextLowLink = newLink++;
						for (int i = 0; i < succCnt; i++) {
							final long nextState = gnode.getStateFP(i);
							final int nextTidx = gnode.getTidx(i);
							final long nextLink = this.dg.getLink(nextState, nextTidx);
							if (nextLink >= 0) {
								if (gnode.getCheckAction(slen, alen, i, eaaction)) {
									if (DiskGraph.isFilePointer(nextLink)) {
										dfsStack.pushLong(nextState);
										dfsStack.pushInt(nextTidx);
										dfsStack.pushLong(nextLink);
									} else if (nextLink < nextLowLink) {
										nextLowLink = nextLink;
									}
								} else if (DiskGraph.isFilePointer(nextLink)) {
									nodeQueue.enqueueLong(nextState);
									nodeQueue.enqueueInt(nextTidx);
									nodeQueue.enqueueLong(nextLink);
								}
							}
						}
						dfsStack.pushLong(nextLowLink);
					} else {
						if (link < lowLink) {
							lowLink = link;
						}
						dfsStack.pushLong(lowLink);
					}
				}
			}
		}

		// After completing the checks, clean up:
		// dfsStack.cleanup();
		// comStack.cleanup();
	}

	/**
	 * For currentPEM, this method checks if the current scc satisfies its AEs
	 * and is fulfilling. (We know the current scc satisfies the pem's EA.) If
	 * satisfiable, this pem contains a counterexample, and this method then
	 * calls printErrorTrace to print an error trace and returns false.
	 */
	private boolean checkComponent(final long state, final int tidx, final MemIntStack comStack) throws IOException {
//		final int comStackSize = comStack.size();
//		Assert.check(comStackSize > 0, EC.GENERAL);
		
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
		TableauNodePtrTable com = new TableauNodePtrTable(128);
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
//		Assert.check(com.size() <= (comStackSize / 5), EC.GENERAL);

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
		int tsz = com.getSize();
		for (int ci = 0; ci < tsz; ci++) {
			int[] nodes = com.getNodesByLoc(ci);
			if (nodes == null) {
				// miss in NotePtrTable (null bucket)
				continue;
			}

			state1 = TableauNodePtrTable.getKey(nodes);
			for (int nidx = 2; nidx < nodes.length; nidx += com.getElemLength()) {
				tidx1 = TableauNodePtrTable.getTidx(nodes, nidx);
				loc1 = TableauNodePtrTable.getElem(nodes, nidx);

				GraphNode curNode = this.dg.getNode(state1, tidx1, loc1);

				// Check AEState:
				for (int i = 0; i < aeslen; i++) {
					if (!AEStateRes[i]) {
						int idx = this.pem.AEState[i];
						AEStateRes[i] = curNode.getCheckState(idx);
					}
				}

				// Check AEAction: A TLA+ action represents the relationship
				// between the current node and a successor state. The current
				// node has n successor states. For each pair, see iff the 
				// successor is in the "com" NodePtrTablecheck, check actions
				// and store the results in AEActionRes(ult).
				int succCnt = curNode.succSize();
				for (int i = 0; i < succCnt; i++) {
					long nextState = curNode.getStateFP(i);
					int nextTidx = curNode.getTidx(i);
					if (com.getLoc(nextState, nextTidx) != -1) {
						for (int j = 0; j < aealen; j++) {
							if (!AEActionRes[j]) {
								int idx = this.pem.AEAction[j];
								AEActionRes[j] = curNode.getCheckAction(slen, alen, i, idx);
							}
						}
					}
				}

				// Check that the component is fulfilling. (See MP page 453.)
				// Note that the promises are precomputed and stored in oos.
				for (int i = 0; i < plen; i++) {
					LNEven promise = this.oos.getPromises()[i];
					TBPar par = curNode.getTNode(this.oos.getTableau()).getPar();
					if (par.isFulfilling(promise)) {
						promiseRes[i] = true;
					}
				}
			}
		}

		// We find a counterexample if all three conditions are satisfied.
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
		// conditions are satisfied. So, print a counter-example!
		if (setErrFound()) {
			this.printTrace(state, tidx, com);
		}
		return false;
	}

	/* Check if the node <state, tidx> stutters. */
	private boolean isStuttering(long state, int tidx, long loc) throws IOException {
		int slen = this.oos.getCheckState().length;
		int alen = this.oos.getCheckAction().length;

		GraphNode gnode = this.dg.getNode(state, tidx, loc);
		int succCnt = gnode.succSize();
		for (int i = 0; i < succCnt; i++) {
			long nextState = gnode.getStateFP(i);
			int nextTidx = gnode.getTidx(i);
			if (state == nextState && tidx == nextTidx) {
				return gnode.getCheckAction(slen, alen, i, this.pem.EAAction);
			}
		}
		return false;
	}

	/**
	 * Print out the error state trace. The method first generates a "bad" cycle
	 * from the current scc, and then generates a prefix path from some initial
	 * state to the "bad" cycle in the state graph. The prefix path and the
	 * "bad" cycle together forms a counter-example.
	 */
	private void printTrace(final long state, final int tidx, final TableauNodePtrTable nodeTbl) throws IOException {

		MP.printError(EC.TLC_TEMPORAL_PROPERTY_VIOLATED);
		MP.printError(EC.TLC_COUNTER_EXAMPLE);

		// First, find a "bad" cycle from the "bad" scc.
		int slen = this.oos.getCheckState().length;
		int alen = this.oos.getCheckAction().length;
		boolean[] AEStateRes = new boolean[this.pem.AEState.length];
		boolean[] AEActionRes = new boolean[this.pem.AEAction.length];
		boolean[] promiseRes = new boolean[this.oos.getPromises().length];
		int cnt = AEStateRes.length + AEActionRes.length + promiseRes.length;

		MemIntStack cycleStack = new MemIntStack(liveCheck.getMetaDir(), "cycle");

		// Mark state as visited:
		int[] nodes = nodeTbl.getNodes(state);
		int tloc = nodeTbl.getIdx(nodes, tidx);
		long ptr = TableauNodePtrTable.getElem(nodes, tloc);
		TableauNodePtrTable.setSeen(nodes, tloc);

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

				// Check AEAction:
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
		long startState = curNode.stateFP;

		if (startState != state) {
			MemIntQueue queue = new MemIntQueue(liveCheck.getMetaDir(), null);
			long curState = startState;
			int ploc = -1;
			int curLoc = nodeTbl.getNodesLoc(curState);
			nodes = nodeTbl.getNodesByLoc(curLoc);
			TableauNodePtrTable.setSeen(nodes);

			_done: while (true) {
				tloc = TableauNodePtrTable.startLoc(nodes);
				while (tloc != -1) {
					int curTidx = TableauNodePtrTable.getTidx(nodes, tloc);
					long curPtr = TableauNodePtrTable.getPtr(TableauNodePtrTable.getElem(nodes, tloc));
					curNode = this.dg.getNode(curState, curTidx, curPtr);
					int succCnt = curNode.succSize();

					for (int j = 0; j < succCnt; j++) {
						long nextState = curNode.getStateFP(j);

						if (nextState == state) {
							// we have found a path from startState to state:
							while (curState != startState) {
								postfix.addElement(curState);
								nodes = nodeTbl.getNodesByLoc(ploc);
								curState = TableauNodePtrTable.getKey(nodes);
								ploc = TableauNodePtrTable.getParent(nodes);
							}
							postfix.addElement(startState);
							break _done;
						}

						int[] nodes1 = nodeTbl.getNodes(nextState);
						if (nodes1 != null && !TableauNodePtrTable.isSeen(nodes1)) {
							TableauNodePtrTable.setSeen(nodes1);
							queue.enqueueLong(nextState);
							queue.enqueueInt(curLoc);
						}
					}
					tloc = TableauNodePtrTable.nextLoc(nodes, tloc);
				}
				TableauNodePtrTable.setParent(nodes, ploc);
				curState = queue.dequeueLong();
				ploc = queue.dequeueInt();
				curLoc = nodeTbl.getNodesLoc(curState);
				nodes = nodeTbl.getNodesByLoc(curLoc);
			}
		}

		// Now, print the error trace. We first construct the prefix that
		// led to the bad cycle. The nodes on prefix and cycleStack then
		// form the complete counter example.
		int stateNum = 0;
		LongVec prefix = this.dg.getPath(state, tidx);
		int plen = prefix.size();
		TLCStateInfo[] states = new TLCStateInfo[plen];

		// Recover the initial state:
		//TODO This throws an ArrayIndexOutOfBounds if getPath returned a
		// LongVec with just a single element. This happens when the parameter
		// state is one of the init states already.
		long fp = prefix.elementAt(plen - 1);
		TLCStateInfo sinfo = liveCheck.getTool().getState(fp);
		if (sinfo == null) {
			throw new EvalException(EC.TLC_FAILED_TO_RECOVER_INIT);
		}
		states[stateNum++] = sinfo;

		// Recover the successor states:
		//TODO Check if path.size has elements
		for (int i = plen - 2; i >= 0; i--) {
			long curFP = prefix.elementAt(i);
			// The prefix might contain duplicates if the path happens to walk
			// along two distinct states which differ in the tableau idx only
			// (same fingerprint). From the counterexample perspective, this is
			// irrelevant.
			if (curFP != fp) {
				sinfo = liveCheck.getTool().getState(curFP, sinfo.state);
				if (sinfo == null) {
					throw new EvalException(EC.TLC_FAILED_TO_RECOVER_NEXT);
				}
				states[stateNum++] = sinfo;
				fp = curFP;
			}
		}

		// Print the prefix:
		TLCState lastState = null;
		for (int i = 0; i < stateNum; i++) {
			StatePrinter.printState(states[i], lastState, i + 1);
			lastState = states[i].state;
		}

		// Print the cycle:
		int cyclePos = stateNum;
		long cycleFP = fp;
		while (cycleStack.size() > 0) {
			postfix.addElement(cycleStack.popLong());
			cycleStack.popInt(); // ignore tableau idx
		}

		// Assert.assert(fps.length > 0);
		for (int i = postfix.size() - 1; i >= 0; i--) {
			long curFP = postfix.elementAt(i);
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

		if (fp == cycleFP) {
			StatePrinter.printStutteringState(++stateNum);
		} else {
			sinfo = liveCheck.getTool().getState(cycleFP, sinfo.state);
			if (sinfo == null) {
				throw new EvalException(EC.TLC_FAILED_TO_RECOVER_NEXT);
			}
			if (TLCGlobals.tool) {
				MP.printState(EC.TLC_BACK_TO_STATE, new String[] { "" + cyclePos }, (TLCState) null, -1);
			} else {
				MP.printMessage(EC.TLC_BACK_TO_STATE, "" + cyclePos);
			}
		}
	}

	public final void run() {
		try {
			while (true) {
				// Get next OOS, and work on it:
				int idx = getNextOOS();
				if (idx == -1 || hasErrFound()) {
					break;
				}

				this.oos = liveCheck.getChecker(idx).getSolution();
				this.dg = liveCheck.getChecker(idx).getDiskGraph();
				this.dg.createCache();
				PossibleErrorModel[] pems = this.oos.getPems();
				for (int i = 0; i < pems.length; i++) {
					if (!hasErrFound()) {
						this.pem = pems[i];
						this.checkSccs();
					}
				}
				this.dg.destroyCache();
			}
		} catch (Exception e) {
			MP.printError(EC.GENERAL, "checking liveness", e); // LL changed
			// call 7 April
			// 2012
			// Assert.printStack(e);
			return;
		}
	}

}
