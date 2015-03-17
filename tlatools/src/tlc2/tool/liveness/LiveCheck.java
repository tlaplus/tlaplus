// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:44 PST by lamport
//      modified on Thu Jan 10 18:41:04 PST 2002 by yuanyu

package tlc2.tool.liveness;

import java.io.IOException;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.Action;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.LongVec;
import tlc2.util.statistics.BucketStatistics;

public class LiveCheck {

	private static Action[] actions;
	protected static Tool myTool;
	protected static String metadir;
	protected static OrderOfSolution[] solutions;
	protected static DiskGraph[] dgraphs;
	public static BucketStatistics outDegreeGraphStats;
	
	// SZ: fields not read locally
	// private static OrderOfSolution currentOOS;
	// private static DiskGraph currentDG;
	// private static PossibleErrorModel currentPEM;

	public static void init(Tool tool, Action[] acts, String mdir) throws IOException {
		myTool = tool;
		actions = acts;
		metadir = mdir;
		solutions = Liveness.processLiveness(myTool, metadir);
		dgraphs = new DiskGraph[solutions.length];
		outDegreeGraphStats = new BucketStatistics("Histogram vertex out-degree", LiveCheck.class.getPackage()
				.getName(), "DiskGraphsOutDegree");
		for (int soln = 0; soln < solutions.length; soln++) {
			dgraphs[soln] = new DiskGraph(metadir, soln, solutions[soln].hasTableau(), outDegreeGraphStats);
			// System.err.println(solutions[soln]);
		}
	}

	/**
	 * This method records that state is an initial state in the behavior graph.
	 * It is called when a new initial state is generated.
	 */
	public static void addInitState(TLCState state, long stateFP) {
		for (int soln = 0; soln < solutions.length; soln++) {
			OrderOfSolution oos = solutions[soln];
			DiskGraph dgraph = dgraphs[soln];
			if (!oos.hasTableau()) {
				// if there is no tableau ...
				dgraph.addInitNode(stateFP, -1);
			} else {
				// if there is tableau ...
				// (state, tnode) is a root node if tnode is an initial tableau
				// node and tnode is consistent with state.
				int initCnt = oos.getTableau().getInitCnt();
				for (int i = 0; i < initCnt; i++) {
					TBGraphNode tnode = oos.getTableau().getNode(i);
					if (tnode.isConsistent(state, myTool)) {
						dgraph.addInitNode(stateFP, tnode.index);
						dgraph.recordNode(stateFP, tnode.index);
					}
				}
			}
		}
	}

	/**
	 * This method adds new nodes into the behavior graph induced by s0. It is
	 * called after the successors of s0 are computed.
	 */
	public static void addNextState(TLCState s0, long fp0, StateVec nextStates, LongVec nextFPs) throws IOException {
		for (int soln = 0; soln < solutions.length; soln++) {
			final OrderOfSolution oos = solutions[soln];
			final DiskGraph dgraph = dgraphs[soln];
			final boolean[] checkStateRes = oos.checkState(s0);
			final int slen = checkStateRes.length;
			final int alen = oos.getCheckAction().length;
			boolean[] checkActionRes = new boolean[alen];

			int cnt = 0;
			synchronized (oos) {
				if (!oos.hasTableau()) {
					// if there is no tableau ...
					final GraphNode node0 = new GraphNode(fp0, -1);
					node0.setCheckState(checkStateRes);
					final int succCnt = nextStates.size();
					for (int sidx = 0; sidx < succCnt; sidx++) {
						final TLCState s1 = nextStates.elementAt(sidx);
						final long fp1 = nextFPs.elementAt(sidx);
						final long ptr1 = dgraph.getPtr(fp1);
						if (ptr1 == -1 || !node0.transExists(fp1, -1)) {
							checkActionRes = oos.checkAction(s0, s1);
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
							node0.addTransition(fp1, -1, slen, alen, checkActionRes, (succCnt - cnt++));
						} else {
							cnt++;
						}
					}
					node0.realign(); // see node0.addTransition() hint
					// Add a node for the current state:
					dgraph.addNode(node0);
				} else {
					// if there is tableau ...
					final int loc0 = dgraph.setDone(fp0);
					final int[] nodes = dgraph.getNodesByLoc(loc0);
					if (nodes == null) {
						continue;
					}
					final int succCnt = nextStates.size();
					// See node0.addTransition(..) of previous case.
					final int allocationHint = ((nodes.length / 3) * succCnt);
					for (int nidx = 2; nidx < nodes.length; nidx += 3) {
						final int tidx0 = nodes[nidx];
						final TBGraphNode tnode0 = oos.getTableau().getNode(tidx0);
						final GraphNode node0 = new GraphNode(fp0, tidx0);
						node0.setCheckState(checkStateRes);
						for (int sidx = 0; sidx < succCnt; sidx++) {
							TLCState s1 = nextStates.elementAt(sidx);
							long fp1 = nextFPs.elementAt(sidx);
							boolean isDone = dgraph.isDone(fp1);
							boolean noActionRes = true;
							for (int k = 0; k < tnode0.nextSize(); k++) {
								TBGraphNode tnode1 = tnode0.nextAt(k);
								long ptr1 = dgraph.getPtr(fp1, tnode1.index);
								if (ptr1 == -1) {
									if (tnode1.isConsistent(s1, myTool)) {
										if (noActionRes) {
											checkActionRes = oos.checkAction(s0, s1);
											noActionRes = false;
										}
										node0.addTransition(fp1, tnode1.index, slen, alen, checkActionRes, allocationHint - cnt++);
										// Record that we have seen <fp1,
										// tnode1>. If fp1 is done, we have
										// to compute the next states for <fp1,
										// tnode1>.
										dgraph.recordNode(fp1, tnode1.index);
										if (isDone) {
											addNextState(s1, fp1, tnode1, oos, dgraph);
										}
									}
								} else if (!node0.transExists(fp1, tnode1.index)) {
									if (noActionRes) {
										checkActionRes = oos.checkAction(s0, s1);
										noActionRes = false;
									}
									node0.addTransition(fp1, tnode1.index, slen, alen, checkActionRes, allocationHint - cnt++);
								} else {
									// Increment cnt even if addTrasition is not called. After all, 
									// the for loop has completed yet another iteration.
									cnt++;
								}
							}
						}
						node0.realign(); // see node0.addTransition() hint
						dgraph.addNode(node0);
					}
				}
			}
		}
	}

	/**
	 * This method takes care of the case that a new node (s, t) is generated
	 * after s has been done. In this case, we will have to compute the children
	 * of (s, t). Hopefully, this case does not occur very frequently.
	 */
	private static void addNextState(TLCState s, long fp, TBGraphNode tnode, OrderOfSolution oos, DiskGraph dgraph)
			throws IOException {
		boolean[] checkStateRes = oos.checkState(s);
		int slen = checkStateRes.length;
		int alen = oos.getCheckAction().length;
		GraphNode node = new GraphNode(fp, tnode.index);
		node.setCheckState(checkStateRes);

		// see allocationHint of node.addTransition() invocations below
		int cnt = 0;
		
		// Add edges induced by s -> s:
		boolean[] checkActionRes = null;
		final int nextSize = tnode.nextSize();
		for (int i = 0; i < nextSize; i++) {
			TBGraphNode tnode1 = tnode.nextAt(i);
			int tidx1 = tnode1.index;
			long ptr1 = dgraph.getPtr(fp, tidx1);
			if (ptr1 == -1) {
				if (tnode1.isConsistent(s, myTool)) {
					if (checkActionRes == null) {
						checkActionRes = new boolean[alen];
						for (int m = 0; m < alen; m++) {
							checkActionRes[m] = oos.getCheckAction()[m].eval(myTool, s, s);
						}
					}
					node.addTransition(fp, tidx1, slen, alen, checkActionRes, (nextSize - cnt++));
					dgraph.recordNode(fp, tnode1.index);
					addNextState(s, fp, tnode1, oos, dgraph);
				} else {
					cnt++;
				}
			} else {
				if (checkActionRes == null) {
					checkActionRes = new boolean[alen];
					for (int m = 0; m < alen; m++) {
						checkActionRes[m] = oos.getCheckAction()[m].eval(myTool, s, s);
					}
				}
				node.addTransition(fp, tidx1, slen, alen, checkActionRes, (nextSize - cnt++));
			}
		}

		// Add edges induced by s -> s1:
		cnt = 0;
		for (int i = 0; i < actions.length; i++) {
			StateVec nextStates = myTool.getNextStates(actions[i], s);
			int nextCnt = nextStates.size();
			for (int j = 0; j < nextCnt; j++) {
				TLCState s1 = nextStates.elementAt(j);
				if (myTool.isInModel(s1) && myTool.isInActions(s, s1)) {
					long fp1 = s1.fingerPrint();
					checkActionRes = null;
					boolean isDone = dgraph.isDone(fp1);
					for (int k = 0; k < tnode.nextSize(); k++) {
						TBGraphNode tnode1 = tnode.nextAt(k);
						int tidx1 = tnode1.index;
						long ptr1 = dgraph.getPtr(fp1, tidx1);
						final int total = actions.length * nextCnt * tnode.nextSize();
						if (ptr1 == -1) {
							if (tnode1.isConsistent(s1, myTool)) {
								if (checkActionRes == null) {
									checkActionRes = new boolean[alen];
									for (int m = 0; m < alen; m++) {
										checkActionRes[m] = oos.getCheckAction()[m].eval(myTool, s, s1);
									}
								}
								node.addTransition(fp1, tidx1, slen, alen, checkActionRes, (total - cnt++));
								// Record that we have seen <fp1, tnode1>. If
								// fp1 is done, we have to compute the next
								// states for <fp1, tnode1>.
								dgraph.recordNode(fp1, tidx1);
								if (isDone) {
									addNextState(s1, fp1, tnode1, oos, dgraph);
								}
							}
						} else if (!node.transExists(fp1, tidx1)) {
							if (checkActionRes == null) {
								checkActionRes = new boolean[alen];
								for (int m = 0; m < alen; m++) {
									checkActionRes[m] = oos.getCheckAction()[m].eval(myTool, s, s1);
								}
							}
							node.addTransition(fp1, tidx1, slen, alen, checkActionRes, (total - cnt++));
						} else {
							cnt++;
						}
					}
				} else {
					cnt++;
				}
			}
		}
		node.realign(); // see node.addTransition() hint
		dgraph.addNode(node);
	}

	/**
	 * Check liveness properties for the current partial state graph. Returns
	 * true iff it finds no errors.
	 */
	public static boolean check() throws Exception {
		int slen = solutions.length;
		int wNum = Math.min(slen, TLCGlobals.getNumWorkers());

		if (wNum == 1) {
			LiveWorker worker = new LiveWorker(0);
			worker.run();
		} else {
			LiveWorker[] workers = new LiveWorker[wNum];
			for (int i = 0; i < wNum; i++) {
				workers[i] = new LiveWorker(i);
				workers[i].start();
			}
			for (int i = 0; i < wNum; i++) {
				workers[i].join();
			}
		}

		if (LiveWorker.hasErrFound()) {
			return false;
		}

		// Reset after checking:
		for (int soln = 0; soln < slen; soln++) {
			dgraphs[soln].makeNodePtrTbl();
		}
		return true;
	}

	/* Close all the files for disk graphs. */
	public static void close() throws IOException {
		for (int i = 0; i < dgraphs.length; i++) {
			dgraphs[i].close();
		}
	}

	/* Checkpoint. */
	public static synchronized void beginChkpt() throws IOException {
		for (int i = 0; i < dgraphs.length; i++) {
			dgraphs[i].beginChkpt();
		}
	}

	public static void commitChkpt() throws IOException {
		for (int i = 0; i < dgraphs.length; i++) {
			dgraphs[i].commitChkpt();
		}
	}

	public static void recover() throws IOException {
		for (int i = 0; i < dgraphs.length; i++) {
			MP.printMessage(EC.TLC_AAAAAAA);
			dgraphs[i].recover();
		}
	}

	public static void calculateInDegreeDiskGraphs(final BucketStatistics aGraphStats) throws IOException {
		for (int i = 0; i < dgraphs.length; i++) {
			final DiskGraph diskGraph = dgraphs[i];
			diskGraph.calculateInDegreeDiskGraph(aGraphStats);
		}
	}
	
	public static void calculateOutDegreeDiskGraphs(final BucketStatistics aGraphStats) throws IOException {
		for (int i = 0; i < dgraphs.length; i++) {
			final DiskGraph diskGraph = dgraphs[i];
			diskGraph.calculateOutDegreeDiskGraph(aGraphStats);
		}
	}
}
