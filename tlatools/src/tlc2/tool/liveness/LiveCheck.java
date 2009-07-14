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

public class LiveCheck {

  private static Action[] actions;
  protected static Tool myTool;
  protected static String metadir;
  protected static OrderOfSolution[] solutions;
  protected static DiskGraph[] dgraphs;

  // SZ: fields not read localy
  // private static OrderOfSolution currentOOS;
  // private static DiskGraph currentDG;
  // private static PossibleErrorModel currentPEM;

  public static void init(Tool tool, Action[] acts, String mdir)
  throws IOException {
    myTool = tool;
    actions = acts;
    metadir = mdir;
    solutions = Liveness.processLiveness(myTool, metadir);
    dgraphs = new DiskGraph[solutions.length];
    for (int soln = 0; soln < solutions.length; soln++) {
      boolean hasTableau = (solutions[soln].tableau != null);
      dgraphs[soln] = new DiskGraph(metadir, soln, hasTableau);
      // System.err.println(solutions[soln]);
    }    
  }

  /**
   * This method records that state is an initial state in the
   * behavior graph. It is called when a new initial state is
   * generated.
   */
  public static void addInitState(TLCState state, long stateFP) {
    for (int soln = 0; soln < solutions.length; soln++) {
      OrderOfSolution oos = solutions[soln];
      DiskGraph dgraph = dgraphs[soln];
      if (oos.tableau == null) {
	// if there is no tableau ...
	dgraph.addInitNode(stateFP, -1);
      }
      else {
	// if there is tableau ...
	// (state, tnode) is a root node if tnode is an initial tableau
	// node and tnode is consistent with state.
	int initCnt = oos.tableau.getInitCnt();
	for (int i = 0; i < initCnt; i++) {
	  TBGraphNode tnode = oos.tableau.getNode(i);
	  if (tnode.isConsistent(state, myTool)) {
	    dgraph.addInitNode(stateFP, tnode.index);
	    dgraph.recordNode(stateFP, tnode.index);
	  }
	}
      }
    }
  }

  /**
   * This method adds new nodes into the behavior graph induced by s0.
   * It is called after the successors of s0 are computed.
   */
  public static void addNextState(TLCState s0, long fp0,
				  StateVec nextStates,
				  LongVec nextFPs)
  throws IOException {
    for (int soln = 0; soln < solutions.length; soln++) {
      OrderOfSolution oos = solutions[soln];
      DiskGraph dgraph = dgraphs[soln];
      int slen = oos.checkState.length;
      int alen = oos.checkAction.length;

      boolean[] checkStateRes = new boolean[slen];
      boolean[] checkActionRes = new boolean[alen];
      for (int i = 0; i < slen; i++) {
	checkStateRes[i] = oos.checkState[i].eval(myTool, s0, null);
      }
      synchronized(oos) {
	if (oos.tableau == null) {
	  // if there is no tableau ...
	  GraphNode node0 = new GraphNode(fp0, -1);
	  node0.setCheckState(checkStateRes);
	  int succCnt = nextStates.size();
	  for (int sidx = 0; sidx < succCnt; sidx++) {
	    TLCState s1 = nextStates.elementAt(sidx);
	    long fp1 = nextFPs.elementAt(sidx);
	    long ptr1 = dgraph.getPtr(fp1);
	    if (ptr1 == -1 || !node0.transExists(fp1, -1)) {
	      for (int i = 0; i < alen; i++) {
		checkActionRes[i] = oos.checkAction[i].eval(myTool, s0, s1);
	      }
	      node0.addTransition(fp1, -1, slen, alen, checkActionRes);
	    }
	  }
	  // Add a node for the current state:
	  dgraph.addNode(node0);
	}
	else {
	  // if there is tableau ...
	  int loc0 = dgraph.setDone(fp0);
	  int[] nodes = dgraph.getNodesByLoc(loc0);
	  if (nodes == null) continue;
	  for (int nidx = 2; nidx < nodes.length; nidx += 3) {
	    int tidx0 = nodes[nidx];
	    TBGraphNode tnode0 = oos.tableau.getNode(tidx0);
	    GraphNode node0 = new GraphNode(fp0, tidx0);
	    node0.setCheckState(checkStateRes);
	    int succCnt = nextStates.size();
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
		      for (int i = 0; i < alen; i++) {
			checkActionRes[i] = oos.checkAction[i].eval(myTool, s0, s1);
		      }
		      noActionRes = false;
		    }
		    node0.addTransition(fp1, tnode1.index, slen, alen, checkActionRes);
		    // Record that we have seen <fp1, tnode1>.  If fp1 is done, we have
		    // to compute the next states for <fp1, tnode1>.
		    dgraph.recordNode(fp1, tnode1.index);
		    if (isDone) {
		      addNextState(s1, fp1, tnode1, oos, dgraph);
		    }
		  }
		}
		else if (!node0.transExists(fp1, tnode1.index)) {
		  if (noActionRes) {
		    for (int i = 0; i < alen; i++) {
		      checkActionRes[i] = oos.checkAction[i].eval(myTool, s0, s1);
		    }
		    noActionRes = false;
		  }
		  node0.addTransition(fp1, tnode1.index, slen, alen, checkActionRes);
		}
	      }
	    }
	    dgraph.addNode(node0);
	  }
	}
      }
    }
  }

  /**
   * This method takes care of the case that a new node (s, t) is
   * generated after s has been done. In this case, we will have to
   * compute the children of (s, t). Hopefully, this case does not
   * occur very frequently.
   */
  private static void addNextState(TLCState s, long fp, TBGraphNode tnode,
				   OrderOfSolution oos, DiskGraph dgraph)
  throws IOException {
    int slen = oos.checkState.length;
    int alen = oos.checkAction.length;
    boolean[] checkStateRes = new boolean[slen];
    for (int m = 0; m < slen; m++) {
      checkStateRes[m] = oos.checkState[m].eval(myTool, s, null);
    }
    GraphNode node = new GraphNode(fp, tnode.index);
    node.setCheckState(checkStateRes);

    // Add edges induced by s -> s:
    boolean[] checkActionRes = null;    
    for (int i = 0; i < tnode.nextSize(); i++) {
      TBGraphNode tnode1 = tnode.nextAt(i);
      int tidx1 = tnode1.index;
      long ptr1 = dgraph.getPtr(fp, tidx1);
      if (ptr1 == -1) {
	if (tnode1.isConsistent(s, myTool)) {
	  if (checkActionRes == null) {
	    checkActionRes = new boolean[alen];
	    for (int m = 0; m < alen; m++) {
	      checkActionRes[m] = oos.checkAction[m].eval(myTool, s, s);
	    }
	  }
	  node.addTransition(fp, tidx1, slen, alen, checkActionRes);
	  dgraph.recordNode(fp, tnode1.index);	  
	  addNextState(s, fp, tnode1, oos, dgraph);
	}
      }
      else {
	if (checkActionRes == null) {
	  checkActionRes = new boolean[alen];
	  for (int m = 0; m < alen; m++) {
	    checkActionRes[m] = oos.checkAction[m].eval(myTool, s, s);
	  }
	}
	node.addTransition(fp, tidx1, slen, alen, checkActionRes);
      }
    }

    // Add edges induced by s -> s1:
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
	    if (ptr1 == -1) {
	      if (tnode1.isConsistent(s1, myTool)) {
		if (checkActionRes == null) {
		  checkActionRes = new boolean[alen];
		  for (int m = 0; m < alen; m++) {
		    checkActionRes[m] = oos.checkAction[m].eval(myTool, s, s1);
		  }
		}
		node.addTransition(fp1, tidx1, slen, alen, checkActionRes);
		// Record that we have seen <fp1, tnode1>.  If fp1 is done,
		// we have to compute the next states for <fp1, tnode1>.
		dgraph.recordNode(fp1, tidx1);
		if (isDone) {
		  addNextState(s1, fp1, tnode1, oos, dgraph);
		}
	      }
	    }
	    else if (!node.transExists(fp1, tidx1)) {
	      if (checkActionRes == null) {
		checkActionRes = new boolean[alen];
		for (int m = 0; m < alen; m++) {
		  checkActionRes[m] = oos.checkAction[m].eval(myTool, s, s1);
		}
	      }
	      node.addTransition(fp1, tidx1, slen, alen, checkActionRes);
	    }
	  }
	}
      }
    }
    dgraph.addNode(node);
  }

  /**
   * Check liveness properties for the current partial state graph.
   * Returns true iff it finds no errors.
   */
  public static boolean check() throws Exception {
    int slen = solutions.length;
    int wNum = Math.min(slen, TLCGlobals.getNumWorkers());

    if (wNum == 1) {
      LiveWorker worker = new LiveWorker(0);
      worker.run();
    }
    else {
      LiveWorker[] workers = new LiveWorker[wNum];
      for (int i = 0; i < wNum; i++) {
	workers[i] = new LiveWorker(i);
	workers[i].start();
      }
      for (int i = 0; i < wNum; i++) {
	workers[i].join();
      }
    }

    if (LiveWorker.hasErrFound()) return false;
    
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

  /* Checkpoint.  */
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

}
