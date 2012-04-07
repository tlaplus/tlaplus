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

public class LiveWorker extends IdThread {

  private static int nextOOS = 0;
  private static int errFoundByThread = -1;
  private static Object workerLock = new Object();

  private OrderOfSolution oos = null;
  private DiskGraph dg = null;
  private PossibleErrorModel pem = null;

  public LiveWorker(int id) { super(id); }
  
  public synchronized static int getNextOOS() {
    if (nextOOS < LiveCheck.solutions.length) {
      return nextOOS++;
    }
    return -1;
  }

  // Returns true iff an error has already found.
  public static boolean hasErrFound() {
    synchronized(workerLock) {
      return (errFoundByThread != -1);
    }
  }

  /**
   * Returns true iff either an error has not found or the error is
   * found by this thread.
   */
  public /* static synchronized */ boolean setErrFound() {
    synchronized(workerLock) {
      if (errFoundByThread == -1) {
        errFoundByThread = this.myGetId(); // GetId();
        return true;
      }
      else if (errFoundByThread == this.myGetId()) {  // (* GetId()) {
        return true;
      }
      return false;
    }
  }

  /**
   * The main routine that computes strongely connected components,
   * and checks each of them to see if it contains a counterexample.
   */
  public final void checkSccs() throws IOException {
    // Initialize this.dg:
    this.dg.makeNodePtrTbl();

    // Initialize nodeQueue with initial states.
    MemIntQueue nodeQueue = new MemIntQueue(LiveCheck.metadir, "root");
    LongVec initNodes = this.dg.getInitNodes();
    int numOfInits = initNodes.size();
    for (int j = 0; j < numOfInits; j += 2) {
      long state = initNodes.elementAt(j);
      int tidx = (int)initNodes.elementAt(j+1);
      long ptr = this.dg.getLink(state, tidx);
      if (ptr >= 0) {
	nodeQueue.enqueueLong(state);
	nodeQueue.enqueueInt(tidx);
	nodeQueue.enqueueLong(ptr);
      }
    }
      
    int[] eaaction = this.pem.EAAction;
    int slen = this.oos.checkState.length;
    int alen = this.oos.checkAction.length;
    MemIntStack dfsStack = new MemIntStack(LiveCheck.metadir, "dfs");
    MemIntStack comStack = new MemIntStack(LiveCheck.metadir, "com");

    // Generate the SCCs and check if they contain any "bad" cycle.
    while (nodeQueue.length() > 0) {
      long state = nodeQueue.dequeueLong();
      int tidx = nodeQueue.dequeueInt();
      long loc = nodeQueue.dequeueLong();

      // Start computing SCCs with <state, tidx> as the root node:
      dfsStack.reset();

      dfsStack.pushLong(state);
      dfsStack.pushInt(tidx);
      dfsStack.pushLong(loc);
      dfsStack.pushLong(DiskGraph.MAX_PTR);
      long newLink = DiskGraph.MAX_PTR;

      while (dfsStack.size() > 2) {
	long lowLink = dfsStack.popLong();
	long curLoc = dfsStack.popLong();
	int curTidx = dfsStack.popInt();
	long curState = dfsStack.popLong();
	if (curLoc < 0) {
	  // The current node is explored iff curLoc < 0.
	  long curLink = this.dg.getLink(curState, curTidx);
	  if (curLink == lowLink) {
	    // The states on the comStack from top to curState form a SCC.
	    // Check for "bad" cycle.
	    boolean isOK = this.checkComponent(curState, curTidx, comStack);
	    if (!isOK) return;
	  }
	  long plowLink = dfsStack.popLong();
	  if (lowLink < plowLink) plowLink = lowLink;
	  dfsStack.pushLong(plowLink);
	}
	else {
	  // Assign newLink to curState:
	  long link = this.dg.putLink(curState, curTidx, newLink);
	  if (link == -1) {
	    // Push curState back onto dfsStack, but make curState explored:
	    dfsStack.pushLong(lowLink);
	    dfsStack.pushLong(curState);
	    dfsStack.pushInt(curTidx);
	    dfsStack.pushLong(-1);
	    
	    // Add curState to comStack:
	    comStack.pushLong(curLoc);
	    comStack.pushInt(curTidx);
	    comStack.pushLong(curState);

	    // Look at all the successors of curState:
	    GraphNode gnode = this.dg.getNode(curState, curTidx, curLoc);
	    int succCnt = gnode.succSize();
	    long nextLowLink = newLink++;
	    for (int i = 0; i < succCnt; i++) {
	      long nextState = gnode.getStateFP(i);
	      int nextTidx = gnode.getTidx(i);
	      long nextLink = this.dg.getLink(nextState, nextTidx);
	      if (nextLink >= 0) {
		if (gnode.getCheckAction(slen, alen, i, eaaction)) {
		  if (DiskGraph.isFilePointer(nextLink)) {
		    dfsStack.pushLong(nextState);
		    dfsStack.pushInt(nextTidx);
		    dfsStack.pushLong(nextLink);
		  }
		  else if (nextLink < nextLowLink) {
		    nextLowLink = nextLink;
		  }
		}
		else if (DiskGraph.isFilePointer(nextLink)) {
		  nodeQueue.enqueueLong(nextState);
		  nodeQueue.enqueueInt(nextTidx);
		  nodeQueue.enqueueLong(nextLink);		
		}
	      }
	    }
	    dfsStack.pushLong(nextLowLink);
	  }
	  else {
	    if (link < lowLink) lowLink = link;
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
   * For currentPEM, this method checks if the current scc satisfies
   * its AEs and is fulfilling. (We know the current scc satisfies the
   * pem's EA.) If satisfiable, this pem contains a counterexample,
   * and this method then calls printErrorTrace to print an error
   * trace and returns false.
   */
  public boolean checkComponent(long state, int tidx, MemIntStack comStack)
  throws IOException {
    long state1 = comStack.popLong();
    int tidx1 = comStack.popInt();
    long loc1 = comStack.popLong();

    // Simply return if the component is trivial:
    if (state1 == state &&
	tidx1 == tidx &&
	!isStuttering(state1, tidx1, loc1)) {
      this.dg.setMaxLink(state, tidx);
      return true;
    }

    // Now, we know we are working on a non-trivial component
    // We first put all the nodes in this component in a hashtable:
    NodePtrTable com = new NodePtrTable(128, true);
    while (true) {
      // Add <state1, tidx1> into com:
      com.put(state1, tidx1, loc1);
      this.dg.setMaxLink(state1, tidx1);

      // Get the next node of the component:
      if (state == state1 && tidx == tidx1) break;

      state1 = comStack.popLong();
      tidx1 = comStack.popInt();
      loc1 = comStack.popLong();
    }     

    // Check this component:
    int slen = this.oos.checkState.length;
    int alen = this.oos.checkAction.length;
    int aeslen = this.pem.AEState.length;
    int aealen = this.pem.AEAction.length;    
    int plen = this.oos.promises.length;
    boolean[] AEStateRes = new boolean[aeslen];
    boolean[] AEActionRes = new boolean[aealen];
    boolean[] promiseRes = new boolean[plen];

    int tsz = com.getSize();
    for (int ci = 0; ci < tsz; ci++) {
      int[] nodes = com.getNodesByLoc(ci);
      if (nodes == null) continue;

      state1 = NodePtrTable.getKey(nodes);
      for (int nidx = 2; nidx < nodes.length; nidx += 3) {
	tidx1 = NodePtrTable.getTidx(nodes, nidx);
	loc1 = NodePtrTable.getElem(nodes, nidx);

	GraphNode curNode = this.dg.getNode(state1, tidx1, loc1);

	// Check AEState:
	for (int i = 0; i < aeslen; i++) {
	  if (!AEStateRes[i]) {
	    int idx = this.pem.AEState[i];
	    AEStateRes[i] = curNode.getCheckState(idx);
	  }
	}

	// Check AEAction:
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
	  LNEven promise = this.oos.promises[i];
	  TBPar par = curNode.getTNode(this.oos.tableau).getPar();
	  if (par.isFulfilling(promise)) {
	    promiseRes[i] = true;
	  }
	}
      }
    }
    
    // We find a counterexample if all three conditions are satisfied.
    for (int i = 0; i < aeslen; i++) {
      if (!AEStateRes[i]) return true;
    }
    for (int i = 0; i < aealen; i++) {
      if (!AEActionRes[i]) return true;
    }
    for (int i = 0; i < plen; i++) {
      if (!promiseRes[i]) return true;
    }
    // This component must contain a counter-example because all three
    // conditions are satisfied. So, print a counter-example!
    if (setErrFound()) 
    {
      this.printTrace(state, tidx, com);
    }
    return false;
  }
  
  /* Check if the node <state, tidx> stutters.  */
  private boolean isStuttering(long state, int tidx, long loc)
  throws IOException {
    int slen = this.oos.checkState.length;
    int alen = this.oos.checkAction.length;

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
   * Print out the error state trace.  The method first generates a
   * "bad" cycle from the current scc, and then generates a prefix
   * path from some initial state to the "bad" cycle in the state
   * graph.  The prefix path and the "bad" cycle together forms a
   * counter-example.
   */
  private void printTrace(long state, int tidx, NodePtrTable nodeTbl)
  throws IOException {
      
      MP.printError(EC.TLC_TEMPORAL_PROPERTY_VIOLATED);
      MP.printError(EC.TLC_COUNTER_EXAMPLE);
      
    // First, find a "bad" cycle from the "bad" scc.
    int slen = this.oos.checkState.length;
    int alen = this.oos.checkAction.length;
    boolean[] AEStateRes = new boolean[this.pem.AEState.length];
    boolean[] AEActionRes = new boolean[this.pem.AEAction.length];
    boolean[] promiseRes = new boolean[this.oos.promises.length];
    int cnt = AEStateRes.length + AEActionRes.length + promiseRes.length;

    MemIntStack cycleStack = new MemIntStack(LiveCheck.metadir, "cycle");

    // Mark state as visited:
    int[] nodes = nodeTbl.getNodes(state);
    int tloc = NodePtrTable.getIdx(nodes, tidx);
    long ptr = NodePtrTable.getElem(nodes, tloc);
    NodePtrTable.setSeen(nodes, tloc);

    GraphNode curNode = this.dg.getNode(state, tidx, ptr);
    while (cnt > 0) {
      int cnt0 = cnt;

      _next:
      while (true) {
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
	for (int i = 0; i < this.oos.promises.length; i++) {
	  LNEven promise = this.oos.promises[i];
	  TBPar par = curNode.getTNode(this.oos.tableau).getPar();
	  if (!promiseRes[i] && par.isFulfilling(promise)) {
	    promiseRes[i] = true;
	    cnt--;
	  }
	}
	if (cnt <= 0) break;

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
	    tloc = NodePtrTable.getIdx(nodes, nextTidx);
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
	    long nextPtr = NodePtrTable.getPtr(NodePtrTable.getElem(nodes, tloc));
	    curNode = this.dg.getNode(nextState, nextTidx, nextPtr);
	    nodeTbl.resetElems();
	    break _next;
	  }

	  if (nodes != null && tloc != -1 && !NodePtrTable.isSeen(nodes, tloc)) {
	    // <nextState, nextTidx> is an unvisited successor of curNode:
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
	  long nextPtr = NodePtrTable.getPtr(NodePtrTable.getElem(nodes1, tloc1));
	  curNode = this.dg.getNode(nextState1, nextTidx1, nextPtr);
	  nodeTbl.resetElems();
	  break;
	}
	
	// Backtrack if all successors of curNode have been visited
	// and no successor can reduce cnt.
	while (!hasUnvisitedSucc) {
	  long curState = cycleStack.popLong();
	  int curTidx = cycleStack.popInt();
	  long curPtr = NodePtrTable.getPtr(nodeTbl.get(curState, curTidx));
	  curNode = this.dg.getNode(curState, curTidx, curPtr);
	  succCnt = curNode.succSize();
	  for (int i = 0; i < succCnt; i++) {
	    nextState2 = curNode.getStateFP(i);
	    nextTidx2 = curNode.getTidx(i);
	    nodes2 = nodeTbl.getNodes(nextState2);
	    if (nodes2 != null) {
	      tloc2 = NodePtrTable.getIdx(nodes2, nextTidx2);
	      if (tloc2 != -1 && !NodePtrTable.isSeen(nodes2, tloc2)) {
		hasUnvisitedSucc = true;
		break;
	      }
	    }
	  }
	}

	// Take curNode -> <nextState2, nextTidx2>. Set nextState2 visited.
	cycleStack.pushInt(curNode.tindex);
	cycleStack.pushLong(curNode.stateFP);
	long nextPtr = NodePtrTable.getPtr(NodePtrTable.getElem(nodes2, tloc2));
	curNode = this.dg.getNode(nextState2, nextTidx2, nextPtr);
	NodePtrTable.setSeen(nodes2, tloc2);
      }
    }

    // All the conditions are satisfied. Find a path from curNode
    // to state to form a cycle. Note that:
    //    1. curNode has not been pushed on cycleStack.
    //    2. nodeTbl is trashed after this operation.
    nodeTbl.resetElems();
    LongVec postfix = new LongVec(16);
    long startState = curNode.stateFP;
    
    if (startState != state) {
      MemIntQueue queue = new MemIntQueue(LiveCheck.metadir, null);
      long curState = startState;
      int ploc = -1;
      int curLoc = nodeTbl.getNodesLoc(curState);
      nodes = nodeTbl.getNodesByLoc(curLoc);
      NodePtrTable.setSeen(nodes);
      
      _done:
      while (true) {
	tloc = NodePtrTable.startLoc(nodes);
	while (tloc != -1) {
	  int curTidx = NodePtrTable.getTidx(nodes, tloc);
	  long curPtr = NodePtrTable.getPtr(NodePtrTable.getElem(nodes, tloc));
	  curNode = this.dg.getNode(curState, curTidx, curPtr);
	  int succCnt = curNode.succSize();

	  for (int j = 0; j < succCnt; j++) {
	    long nextState = curNode.getStateFP(j);

	    if (nextState == state) {
	      // we have found a path from startState to state:
	      while (curState != startState) {
		postfix.addElement(curState);
		nodes = nodeTbl.getNodesByLoc(ploc);
		curState = NodePtrTable.getKey(nodes);		
		ploc = NodePtrTable.getParent(nodes);		
	      }
	      postfix.addElement(startState);
	      break _done;
	    }

	    int[] nodes1 = nodeTbl.getNodes(nextState);
	    if (nodes1 != null && !NodePtrTable.isSeen(nodes1)) {
	      NodePtrTable.setSeen(nodes1);
	      queue.enqueueLong(nextState);
	      queue.enqueueInt(curLoc);
	    }
	  }
	  tloc = NodePtrTable.nextLoc(nodes, tloc);
	}
	NodePtrTable.setParent(nodes, ploc);
	curState = queue.dequeueLong();
	ploc = queue.dequeueInt();
	curLoc = nodeTbl.getNodesLoc(curState);
	nodes = nodeTbl.getNodesByLoc(curLoc);
      }
    }
    
    // Now, print the error trace. We first construct the prefix that
    // led to the bad cycle.  The nodes on prefix and cycleStack then
    // form the complete counter example.
    int stateNum = 0;
    LongVec prefix = this.dg.getPath(state);
    int plen = prefix.size();
    TLCStateInfo[] states = new TLCStateInfo[plen];

    // Recover the initial state:
    long fp = prefix.elementAt(plen-1);
    TLCStateInfo sinfo = LiveCheck.myTool.getState(fp);
    if (sinfo == null) {
      throw new EvalException(EC.TLC_FAILED_TO_RECOVER_INIT);
    }
    states[stateNum++] = sinfo;

    // Recover the successor states:
    for (int i = plen-2; i >= 0; i--) {
      long curFP = prefix.elementAt(i);
      if (curFP != fp) {
	sinfo = LiveCheck.myTool.getState(curFP, sinfo.state);
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
      StatePrinter.printState(states[i], lastState, i+1);
      lastState = states[i].state;
    }

    // Print the cycle:
    int cyclePos = stateNum;
    long cycleFP = fp;
    while (cycleStack.size() > 0) {
      postfix.addElement(cycleStack.popLong());
      cycleStack.popInt();
    }

    // Assert.assert(fps.length > 0);
    for (int i = postfix.size()-1; i >= 0; i--) {
      long curFP = postfix.elementAt(i);
      if (curFP != fp) {
	sinfo = LiveCheck.myTool.getState(curFP, sinfo.state);
	if (sinfo == null) {
	  throw new EvalException(EC.TLC_FAILED_TO_RECOVER_NEXT);
	}
	StatePrinter.printState(sinfo, lastState, ++stateNum);
	lastState = sinfo.state;
	fp = curFP;
      }
    }

    if (fp == cycleFP) 
    {
        StatePrinter.printStutteringState(++stateNum);
    } else 
    {
      sinfo = LiveCheck.myTool.getState(cycleFP, sinfo.state);
      if (sinfo == null) 
      {
          throw new EvalException(EC.TLC_FAILED_TO_RECOVER_NEXT);
      }
      if (TLCGlobals.tool)
      {
          MP.printState(EC.TLC_BACK_TO_STATE, new String[] { "" + cyclePos } );
      } else
      {
          StatePrinter.printState(sinfo, null, (++stateNum));
          // SZ Jul 10, 2009: replaced with state printer
          // ToolIO.err.println("STATE " + (++stateNum) + ": " + sinfo.info);
          MP.printMessage(EC.TLC_BACK_TO_STATE, "" + cyclePos);
      }
    }
  }

  public final void run() 
  {
      try {
          while (true) {
              // Get next OOS, and work on it:
              int idx = getNextOOS();
              if (idx == -1 || hasErrFound()) break;

              this.oos = LiveCheck.solutions[idx];
              this.dg = LiveCheck.dgraphs[idx];
              this.dg.createCache();
              PossibleErrorModel[] pems = this.oos.pems;
              for (int i = 0; i < pems.length; i++) {
                  if (!hasErrFound()) {
                      this.pem = pems[i];
                      this.checkSccs();
                  }
              }
              this.dg.destroyCache();
          }
      }
      catch (Exception e) 
      {
          MP.printError(EC.GENERAL, "checking liveness", e);  // LL changed call 7 April 2012
          // Assert.printStack(e);
          return;
      }
  }

}
