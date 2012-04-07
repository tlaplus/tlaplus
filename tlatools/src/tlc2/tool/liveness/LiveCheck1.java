// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:44 PST by lamport
//      modified on Fri Jan  4 00:30:06 PST 2002 by yuanyu

package tlc2.tool.liveness;

import java.io.IOException;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.StatePrinter;
import tlc2.tool.Action;
import tlc2.tool.EvalException;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.Tool;
import tlc2.util.FP64;
import tlc2.util.LongObjTable;
import tlc2.util.MemObjectStack;
import tlc2.util.ObjectStack;
import tlc2.util.Vect;

public class LiveCheck1 {
  /**
   * Implementation of liveness checking based on MP book.
   */
  private static Tool myTool;
  private static String metadir;
  private static Action[] actions;
  private static OrderOfSolution[] solutions;
  private static BEGraph[] bgraphs;

  private static TLCState[] stateTrace = null;
  private static int stateTraceLen = -1;
  
  /* The following are the data needed in the scc search.  */
  private static final long MAX_FIRST = 0x2000000000000000L;
  private static final long MAX_SECOND = 0x5000000000000000L;

  private static OrderOfSolution currentOOS = null;
  private static PossibleErrorModel currentPEM = null;
  private static ObjectStack comStack = null;

  /* firstNum ranges from 1 to MAX_FIRST.  */
  private static long firstNum = 1;

  /* secondNum ranges from MAX_FIRST+1 to MAX_SECOND. */
  private static long secondNum = MAX_FIRST + 1;
  private static long startSecondNum = secondNum;

  /* thirdNum ranges from MAX_SECOND+1 to MAX_VALUE.  */
  private static long thirdNum = MAX_SECOND + 1;
  private static long startThirdNum = thirdNum;
  
  /* The number assigned to a new component found by checkSccs. */
  private static long numFirstCom = secondNum;

  /**
   * The starting number assigned to new components found by the
   * many checkSccs1 calls.
   */
  private static long numSecondCom = thirdNum;

  /**
   * The initial state used for the current checking.  It is used in
   * generating the error trace.
   */
  private static BEGraphNode initNode = null;
  
  public static void init(Tool tool, Action[] acts, String mdir) {
    myTool = tool;
    metadir = mdir;
    actions = acts;
    solutions = Liveness.processLiveness(myTool, metadir);
    bgraphs = new BEGraph[solutions.length];
    for (int i = 0; i < solutions.length; i++) {
      bgraphs[i] = new BEGraph(metadir, solutions[i].tableau != null);
    }
  }

  public static void initSim(Tool tool) {
    myTool = tool;
    actions = null;
    solutions = Liveness.processLiveness(myTool, metadir);
  }

  /**
   * This method resets the behavior graph so that we can
   * recompute the SCCs.
   */
  public static void reset() {
    for (int i = 0; i < bgraphs.length; i++) {
      bgraphs[i].resetNumberField();
    }
  }

  private static void initSccParams(OrderOfSolution os) {
    currentOOS = os;
    comStack = new MemObjectStack(metadir, "comstack");
    firstNum = 1;
    secondNum = MAX_FIRST + 1;
    thirdNum = MAX_SECOND + 1;
    startSecondNum = secondNum;
    startThirdNum = thirdNum;
    numFirstCom = secondNum;
    numSecondCom = thirdNum;
  }

  /**
   * This method constructs the behavior graph from an OrderOfSolution
   * and a state trace (a sequence of states). Assume trace.length > 0.
   * It returns the set of initial states.
   */
  static Vect constructBEGraph(OrderOfSolution os) {
    Vect initNodes = new Vect(1);
    int slen = os.checkState.length;
    int alen = os.checkAction.length;
    TLCState srcState = stateTrace[0];     // the initial state
    long srcFP = srcState.fingerPrint();
    boolean[] checkStateRes = new boolean[slen];
    for (int i = 0; i < slen; i++) {
      checkStateRes[i] = os.checkState[i].eval(myTool, srcState, null);
    }
    boolean[] checkActionRes = new boolean[alen];
    for (int i = 0; i < alen; i++) {
      checkActionRes[i] = os.checkAction[i].eval(myTool, srcState, srcState);
    }
    if (os.tableau == null) {
      // If there is no tableau, construct begraph with trace.
      LongObjTable allNodes = new LongObjTable(127);
      BEGraphNode srcNode = new BEGraphNode(srcFP);
      srcNode.setCheckState(checkStateRes);
      srcNode.addTransition(srcNode, slen, alen, checkActionRes);
      allNodes.put(srcFP, srcNode);
      initNodes.addElement(srcNode);
      for (int i = 1; i < stateTraceLen; i++) {
	TLCState destState = stateTrace[i];
	long destFP = destState.fingerPrint();
	BEGraphNode destNode = (BEGraphNode)allNodes.get(destFP);
	if (destNode == null) {
	  destNode = new BEGraphNode(destFP);
	  for (int j = 0; j < slen; j++) {
	    checkStateRes[j] = os.checkState[j].eval(myTool, srcState, null);
	  }
	  destNode.setCheckState(checkStateRes);
	  for (int j = 0; j < alen; j++) {
	    checkActionRes[j] = os.checkAction[j].eval(myTool, destState, destState);
	  }
	  destNode.addTransition(destNode, slen, alen, checkActionRes);
	  for (int j = 0; j < alen; j++) {
	    checkActionRes[j] = os.checkAction[j].eval(myTool, srcState, destState);
	  }
	  srcNode.addTransition(destNode, slen, alen, checkActionRes);
	  allNodes.put(destFP, destNode);	  
	}
	else if (!srcNode.transExists(destNode)) {
	  for (int j = 0; j < alen; j++) {
	    checkActionRes[j] = os.checkAction[j].eval(myTool, srcState, destState);
	  }
	  srcNode.addTransition(destNode, slen, alen, checkActionRes);
	}
	srcNode = destNode;
	srcState = destState;
      }
    }
    else {
      // If there is tableau, construct begraph of (tableau X trace).
      LongObjTable allNodes = new LongObjTable(255);
      Vect srcNodes = new Vect();
      int initCnt = os.tableau.getInitCnt();
      for (int i = 0; i < initCnt; i++) {
	TBGraphNode tnode = os.tableau.getNode(i);
	if (tnode.isConsistent(srcState, myTool)) {
	  BEGraphNode destNode = new BTGraphNode(srcFP, tnode.index);
	  destNode.setCheckState(checkStateRes);
	  initNodes.addElement(destNode);
	  srcNodes.addElement(destNode);
	  allNodes.put(FP64.Extend(srcFP, tnode.index), destNode);
	}
      }
      for (int i = 0; i < srcNodes.size(); i++) {
	BEGraphNode srcNode = (BEGraphNode)srcNodes.elementAt(i);
	TBGraphNode tnode = srcNode.getTNode(os.tableau);
	for (int j = 0; j < tnode.nextSize(); j++) {
	  TBGraphNode tnode1 = tnode.nextAt(j);
	  long destFP = FP64.Extend(srcFP, tnode1.index);
	  BEGraphNode destNode = (BEGraphNode)allNodes.get(destFP);
	  if (destNode != null) {
	    srcNode.addTransition(destNode, slen, alen, checkActionRes);
	  }
	}
      }
      for (int i = 1; i < stateTraceLen; i++) {
	Vect destNodes = new Vect();
	TLCState destState = stateTrace[i];
	long destStateFP = destState.fingerPrint();
	for (int j = 0; j < slen; j++) {
	  checkStateRes[j] = os.checkState[j].eval(myTool, destState, null);
	}
	for (int j = 0; j < alen; j++) {
	  checkActionRes[j] = os.checkAction[j].eval(myTool, srcState, destState);
	}
	for (int j = 0; j < srcNodes.size(); j++) {
	  BEGraphNode srcNode = (BEGraphNode)srcNodes.elementAt(j);
	  TBGraphNode tnode = srcNode.getTNode(os.tableau);
	  for (int k = 0; k < tnode.nextSize(); k++) {
	    TBGraphNode tnode1 = tnode.nextAt(k);
	    long destFP = FP64.Extend(destStateFP, tnode1.index);
	    BEGraphNode destNode = (BEGraphNode)allNodes.get(destFP);
	    if (destNode == null) {
	      if (tnode1.isConsistent(destState, myTool)) {
		destNode = new BTGraphNode(destStateFP, tnode1.index);
		destNode.setCheckState(checkStateRes);
		srcNode.addTransition(destNode, slen, alen, checkActionRes);
		destNodes.addElement(destNode);
		allNodes.put(destFP, destNode);
	      }
	    }
	    else if (!srcNode.transExists(destNode)) {
	      srcNode.addTransition(destNode, slen, alen, checkActionRes);
	    }
	  }
	}
	for (int j = 0; j < alen; j++) {
	  checkActionRes[j] = os.checkAction[j].eval(myTool, destState, destState);
	}
	for (int j = 0; j < destNodes.size(); j++) {
	  BEGraphNode srcNode = (BEGraphNode)destNodes.elementAt(j);
	  TBGraphNode tnode = srcNode.getTNode(os.tableau);
	  for (int k = 0; k < tnode.nextSize(); k++) {
	    TBGraphNode tnode1 = tnode.nextAt(k);
	    long destFP = FP64.Extend(destStateFP, tnode1.index);
	    BEGraphNode destNode = (BEGraphNode)allNodes.get(destFP);
	    if (destNode == null) {
	      if (tnode1.isConsistent(destState, myTool)) {
		destNode = new BTGraphNode(destStateFP, tnode1.index);
		destNode.setCheckState(checkStateRes);
		srcNode.addTransition(destNode, slen, alen, checkActionRes);
		destNodes.addElement(destNode);
		allNodes.put(destFP, destNode);
	      }
	    }
	    else if (!srcNode.transExists(destNode)) {
	      srcNode.addTransition(destNode, slen, alen, checkActionRes);
	    }
	  }
	}
	srcNodes = destNodes;
	srcState = destState;
      }
    }
    return initNodes;
  }

  /**
   * This method adds new nodes into the behavior graph when a new
   * initial state is generated.
   */
  public static void addInitState(TLCState state, long stateFP) {
    for (int soln = 0; soln < solutions.length; soln++) {
      OrderOfSolution os = solutions[soln];
      BEGraph bgraph = bgraphs[soln];
      int slen = os.checkState.length;
      int alen = os.checkAction.length;
      boolean[] checkStateRes = new boolean[slen];
      boolean[] checkActionRes = new boolean[alen];
      for (int i = 0; i < slen; i++) {
	checkStateRes[i] = os.checkState[i].eval(myTool, state, null);
      }
      for (int i = 0; i < alen; i++) {
	checkActionRes[i] = os.checkAction[i].eval(myTool, state, state);
      }
      // Adding nodes and transitions:
      if (os.tableau == null) {
	// if there is no tableau ...
	BEGraphNode node = new BEGraphNode(stateFP);
	node.setCheckState(checkStateRes);
	bgraph.addInitNode(node);
	node.addTransition(node, slen, alen, checkActionRes);
	bgraph.allNodes.putBENode(node);
      }
      else {
	// if there is tableau ...
	// Add edges induced by root --> state:
	int initCnt = os.tableau.getInitCnt();
	for (int i = 0; i < initCnt; i++) {
	  TBGraphNode tnode = os.tableau.getNode(i);
	  if (tnode.isConsistent(state, myTool)) {
	    BTGraphNode destNode = new BTGraphNode(stateFP, tnode.index);
	    destNode.setCheckState(checkStateRes);
	    bgraph.addInitNode(destNode);
	    bgraph.allNodes.putBTNode(destNode);
	    // Add edges induced by state --> state:
	    addNodesForStut(state, stateFP, destNode, checkStateRes,
			    checkActionRes, os, bgraph);
	  }
	}
      }
      // we are done with this state:
      bgraph.allNodes.setDone(stateFP);
    }
  }

  /**
   * This method adds new nodes into the behavior graph when a
   * new state is generated.  The argument s2 is the new state.
   * The argument s1 is parent state of s2.
   */
  public synchronized static void addNextState(TLCState s1, long fp1,
					       TLCState s2, long fp2) {
    for (int soln = 0; soln < solutions.length; soln++) {
      OrderOfSolution os = solutions[soln];
      BEGraph bgraph = bgraphs[soln];
      int slen = os.checkState.length;
      int alen = os.checkAction.length;
      // Adding node and transitions:
      if (os.tableau == null) {
	// if there is no tableau ...
	BEGraphNode node1 = bgraph.allNodes.getBENode(fp1);
	BEGraphNode node2 = bgraph.allNodes.getBENode(fp2);
	if (node2 == null) {
	  node2 = new BEGraphNode(fp2);
	  boolean[] checkStateRes = new boolean[slen];
	  for (int i = 0; i < slen; i++) {
	    checkStateRes[i] = os.checkState[i].eval(myTool, s2, null);
	  }
	  node2.setCheckState(checkStateRes);
	  boolean[] checkActionRes = new boolean[alen];
	  for (int i = 0; i < alen; i++) {
	    checkActionRes[i] = os.checkAction[i].eval(myTool, s1, s2);
	  }
	  node1.addTransition(node2, slen, alen, checkActionRes);
	  for (int i = 0; i < alen; i++) {
	    checkActionRes[i] = os.checkAction[i].eval(myTool, s2, s2);
	  }
	  node2.addTransition(node2, slen, alen, checkActionRes);
	  bgraph.allNodes.putBENode(node2);
	}
	else if (!node1.transExists(node2)) {
	  boolean[] checkActionRes = new boolean[alen];
	  for (int i = 0; i < alen; i++) {
	    checkActionRes[i] = os.checkAction[i].eval(myTool, s1, s2);
	  }
	  node1.addTransition(node2, slen, alen, checkActionRes);
	}
      }
      else {
	// if there is tableau ...
	BTGraphNode[] srcNodes = bgraph.allNodes.getBTNode(fp1);
	if (srcNodes == null) continue;    // nothing to add
	boolean[] checkStateRes = null;
	// Add edges induced by s1 --> s2:
	boolean[] checkActionRes = new boolean[alen];
	for (int i = 0; i < alen; i++) {
	  checkActionRes[i] = os.checkAction[i].eval(myTool, s1, s2);
	}
	boolean[] checkActionRes1 = null;	
	for (int i = 0; i < srcNodes.length; i++) {
	  BTGraphNode srcNode = srcNodes[i];
	  TBGraphNode tnode = os.tableau.getNode(srcNode.getIndex());
	  for (int j = 0; j < tnode.nextSize(); j++) {
	    TBGraphNode tnode1 = tnode.nextAt(j);
	    BTGraphNode destNode = bgraph.allNodes.getBTNode(fp2, tnode1.index);
	    if (destNode == null) {
	      if (tnode1.isConsistent(s2, myTool)) {
		destNode = new BTGraphNode(fp2, tnode1.index);
		if (checkStateRes == null) {
		  checkStateRes = new boolean[slen];
		  for (int k = 0; k < slen; k++) {
		    checkStateRes[k] = os.checkState[k].eval(myTool, s2, null);
		  }
		}
		destNode.setCheckState(checkStateRes);
		srcNode.addTransition(destNode, slen, alen, checkActionRes);
		int idx = bgraph.allNodes.putBTNode(destNode);
		// add edges induced by s2 --> s2:
		if (checkActionRes1 == null) {
		  checkActionRes1 = new boolean[alen];
		  for (int k = 0; k < alen; k++) {
		    checkActionRes1[k] = os.checkAction[k].eval(myTool, s2, s2);
		  }
		}
		addNodesForStut(s2, fp2, destNode, checkStateRes,
				checkActionRes1, os, bgraph);
		// if s2 is done, we have to do something for destNode:
		if (bgraph.allNodes.isDone(idx)) {
		  addNextState(s2, fp2, destNode, os, bgraph);
		}
	      }
	    }
	    else if (!srcNode.transExists(destNode)) {	      
	      srcNode.addTransition(destNode, slen, alen, checkActionRes);
	    }
	  }
	}
      }
    }
  }

  /**
   * This method is called for each new node created. It generates nodes
   * induced by a stuttering state transition.
   */
  private static void addNodesForStut(TLCState state, long fp, BTGraphNode node,
				      boolean[] checkState, boolean[] checkAction,
				      OrderOfSolution os, BEGraph bgraph) {
    int slen = os.checkState.length;
    int alen = os.checkAction.length;
    TBGraphNode tnode = node.getTNode(os.tableau);
    for (int i = 0; i < tnode.nextSize(); i++) {
      TBGraphNode tnode1 = tnode.nextAt(i);
      BTGraphNode destNode = bgraph.allNodes.getBTNode(fp, tnode1.index);
      if (destNode == null) {
	if (tnode1.isConsistent(state, myTool)) {
	  destNode = new BTGraphNode(fp, tnode1.index);
	  destNode.setCheckState(checkState);
	  node.addTransition(destNode, slen, alen, checkAction);  
	  bgraph.allNodes.putBTNode(destNode);
	  addNodesForStut(state, fp, destNode, checkState, checkAction, os, bgraph);
	}
      }
      else {
	node.addTransition(destNode, slen, alen, checkAction);
      }
    }
  }
  
  /**
   * This method takes care of the case that a new node (s, t) is
   * generated after s has been done.  So, we still have to compute
   * the children of (s, t). Hopefully, this case will not occur
   * very frequently.
   */
  private static void addNextState(TLCState s, long fp, BTGraphNode node,
				   OrderOfSolution os, BEGraph bgraph) {
    TBGraphNode tnode = node.getTNode(os.tableau);
    int slen = os.checkState.length;
    int alen = os.checkAction.length;
    boolean[] checkStateRes = null;
    boolean[] checkActionRes = null;
    for (int i = 0; i < actions.length; i++) {
      Action curAction = actions[i];
      StateVec nextStates = myTool.getNextStates(curAction, s);
      for (int j = 0; j < nextStates.size(); j++) {
	// Add edges induced by s -> s1:
	TLCState s1 = nextStates.elementAt(j);
	long fp1 = s1.fingerPrint();
	boolean[] checkActionRes1 = null;	
	for (int k = 0; k < tnode.nextSize(); k++) {
	  TBGraphNode tnode1 = tnode.nextAt(k);
	  BTGraphNode destNode = bgraph.allNodes.getBTNode(fp1, tnode1.index);
	  if (destNode == null) {
	    if (tnode1.isConsistent(s1, myTool)) {
	      destNode = new BTGraphNode(fp1, tnode1.index);
	      if (checkStateRes == null) {
		checkStateRes = new boolean[slen];
		for (int m = 0; m < slen; m++) {
		  checkStateRes[m] = os.checkState[m].eval(myTool, s1, null);
		}
	      }
	      if (checkActionRes == null) {
		checkActionRes = new boolean[alen];
		for (int m = 0; m < alen; m++) {
		  checkActionRes[m] = os.checkAction[m].eval(myTool, s, s1);
		}
	      }
	      destNode.setCheckState(checkStateRes);
	      node.addTransition(destNode, slen, alen, checkActionRes);
	      if (checkActionRes1 == null) {
		checkActionRes1 = new boolean[alen];
		for (int m = 0; m < alen; m++) {
		  checkActionRes1[m] = os.checkAction[m].eval(myTool, s1, s1);
		}
	      }	      
	      addNodesForStut(s1, fp1, destNode, checkStateRes, checkActionRes1,
			      os, bgraph);
	      int idx = bgraph.allNodes.putBTNode(destNode);
	      if (bgraph.allNodes.isDone(idx)) {
		addNextState(s1, fp1, destNode, os, bgraph);
	      }
	    }
	  }
	  else if (!node.transExists(destNode)) {
	    if (checkActionRes == null) {
	      checkActionRes = new boolean[alen];
	      for (int m = 0; m < alen; m++) {
		checkActionRes[m] = os.checkAction[m].eval(myTool, s, s1);
	      }
	    }
	    node.addTransition(destNode, slen, alen, checkActionRes);
	  }
	}
      }
    }
  }

  public synchronized static void setDone(long fp) {
    for (int soln = 0; soln < solutions.length; soln++) {
      bgraphs[soln].allNodes.setDone(fp);
    }
  }

  /**
   * Checks if the partial behavior graph constructed up to now contains
   * any "bad" cycle. A "bad" cycle gives rise to a violation of liveness
   * property.
   */
  public synchronized static void check() {
    int slen = solutions.length;
    if (slen == 0) return;

    for (int soln = 0; soln < slen; soln++) {
      OrderOfSolution oos = solutions[soln];

      // Liveness.printTBGraph(oos.tableau);
      // ToolIO.err.println(bgraphs[soln].toString());

      // We now compute the SCCs of the graph. If we find any SCC
      // that is fulfilling and satisfies any of PEM's, then that
      // SCC contains a "bad" cycle.
      initSccParams(oos);
      BEGraph bgraph = bgraphs[soln];
      int numOfInits = bgraph.initSize();
      for (int i = 0; i < numOfInits; i++) {
	initNode = bgraph.getInitNode(i);
	if (initNode.getNumber() == 0) {
	  checkSccs(initNode);
	}
      }
    }
  }

  /**
   * Checks if the behavior graph constructed from a state trace
   * contains any "bad" cycle.
   */
  public static void checkTrace(TLCState[] trace, int traceLen) {
    stateTrace = trace;
    stateTraceLen = traceLen;
    for (int soln = 0; soln < solutions.length; soln++) {
      OrderOfSolution os = solutions[soln];
      Vect initNodes = constructBEGraph(os);

      // Liveness.printTBGraph(os.tableau);
      // ToolIO.err.println(os.behavior.toString());

      // We now compute the SCCs of the graph. If we find any SCC
      // that is fulfilling and satisfies any of PEM's, then that
      // SCC contains a "bad" cycle.
      initSccParams(os);
      int numOfInits = initNodes.size();
      for (int i = 0; i < numOfInits; i++) {
	initNode = (BEGraphNode)initNodes.elementAt(i);
	if (initNode.getNumber() == 0) {
	  checkSccs(initNode);
	}
      }
    }
  }

  /* Print out the error state trace.  */
  static void printErrorTrace(BEGraphNode node) throws IOException 
  {
      MP.printError(EC.TLC_TEMPORAL_PROPERTY_VIOLATED);
      MP.printError(EC.TLC_COUNTER_EXAMPLE);
    // First, find a "bad" cycle from the "bad" scc.
    ObjectStack cycleStack = new MemObjectStack(metadir, "cyclestack");
    int slen = currentOOS.checkState.length;
    int alen = currentOOS.checkAction.length;
    long lowNum = thirdNum - 1;
    boolean[] AEStateRes = new boolean[currentPEM.AEState.length];
    boolean[] AEActionRes = new boolean[currentPEM.AEAction.length];
    boolean[] promiseRes = new boolean[currentOOS.promises.length];
    int cnt = AEStateRes.length + AEActionRes.length + promiseRes.length;
    BEGraphNode curNode = node;
    while (cnt > 0) {
      curNode.setNumber(thirdNum);
      int cnt0 = cnt;      
    _next:
      while (true) {
	// Check AEState:
	for (int i = 0; i < currentPEM.AEState.length; i++) {
	  int idx = currentPEM.AEState[i];
	  if (!AEStateRes[i] && curNode.getCheckState(idx)) {
	    AEStateRes[i] = true;
	    cnt--;
	  }
	}
	// Check if the component is fulfilling. (See MP page 453.)
	// Note that the promises are precomputed and stored in oos.
	for (int i = 0; i < currentOOS.promises.length; i++) {
	  LNEven promise = currentOOS.promises[i];
	  TBPar par = curNode.getTNode(currentOOS.tableau).getPar();
	  if (!promiseRes[i] && par.isFulfilling(promise)) {
	    promiseRes[i] = true;
	    cnt--;
	  }
	}
	if (cnt <= 0) break;
	// Check AEAction:
	BEGraphNode nextNode1 = null;
	BEGraphNode nextNode2 = null;
	int cnt1 = cnt;
	for (int i = 0; i < curNode.nextSize(); i++) {
	  BEGraphNode node1 = curNode.nextAt(i);
	  long num = node1.getNumber();
	  if (lowNum <= num && num <= thirdNum) {
	    nextNode1 = node1;
	    for (int j = 0; j < currentPEM.AEAction.length; j++) {
	      int idx = currentPEM.AEAction[j];
	      if (!AEActionRes[j] && curNode.getCheckAction(slen, alen, i, idx)) {
		AEActionRes[j] = true;
		cnt--;
	      }
	    }
	  }
	  if (cnt < cnt1) {
	    cycleStack.push(curNode);
	    curNode = node1;
	    thirdNum++;
	    break _next;
	  }
	  if (lowNum <= num && num < thirdNum) nextNode2 = node1;
	}
	if (cnt < cnt0) {
	  cycleStack.push(curNode);
	  curNode = nextNode1;
	  thirdNum++;
	  break;
	}
	// Backtrack if needed:
	while (nextNode2 == null) {
	  curNode = (BEGraphNode)cycleStack.pop();
	  for (int i = 0; i < curNode.nextSize(); i++) {
	    BEGraphNode node1 = curNode.nextAt(i);
	    long num = node1.getNumber();
	    if (lowNum <= num && num < thirdNum) {
	      cycleStack.push(curNode);
	      nextNode2 = node1;
	      break;
	    }
	  }
	}
	cycleStack.push(curNode);
	curNode = nextNode2;
	curNode.setNumber(thirdNum);
      }
    }
    // Close the path to form a cycle. curNode has not been pushed on cycleStack.
    curNode.setNumber(++thirdNum);
  _done:
    while (curNode != node) {
      boolean found = false;
      for (int i = 0; i < curNode.nextSize(); i++) {
	BEGraphNode nextNode = curNode.nextAt(i);
	long num = nextNode.getNumber();
	if (lowNum <= num && num < thirdNum) {
	  cycleStack.push(curNode);
	  if (nextNode == node) {
	    break _done;
	  }
	  found = true;
	  curNode = nextNode;
	  curNode.setNumber(thirdNum);
	  break;
	}
      }
      if (!found) {
	curNode = (BEGraphNode)cycleStack.pop();
      }
    }
    if (cycleStack.size() == 0) {
      cycleStack.push(curNode);
    }

    // Now, print the error trace. We first construct the prefix that
    // led to the bad cycle.  The nodes on prefix and cycleStack then
    // form the complete counter example.
    int stateNum = 0;
    BEGraphNode[] prefix = BEGraph.getPath(initNode, node);
    TLCStateInfo[] states = new TLCStateInfo[prefix.length];

    // Recover the initial state:
    long fp = prefix[0].stateFP;
    TLCStateInfo sinfo = myTool.getState(fp);
    if (sinfo == null) {
      throw new EvalException(EC.TLC_FAILED_TO_RECOVER_INIT);
    }
    states[stateNum++] = sinfo;

    // Recover the successor states:
    for (int i = 1; i < states.length; i++) {
      long fp1 = prefix[i].stateFP;
      if (fp1 != fp) {
	sinfo = myTool.getState(fp1, sinfo.state);
	if (sinfo == null) {
	  throw new EvalException(EC.TLC_FAILED_TO_RECOVER_NEXT);
	}
	states[stateNum++] = sinfo;
      }
      fp = fp1;
    }

    // Print the prefix:
    TLCState lastState = null;    
    for (int i = 0; i < stateNum; i++) {
      StatePrinter.printState(states[i], lastState, i+1);
      lastState = states[i].state;
    }

    // Print the cycle:
    int cyclePos = stateNum;
    long[] fps = new long[cycleStack.size()];
    int idx = fps.length;
    while (idx > 0) {
      fps[--idx] = ((BEGraphNode)cycleStack.pop()).stateFP;
    }
    // Assert.assert(fps.length > 0);
    sinfo = states[stateNum-1];
    for (int i = 1; i < fps.length; i++) {
      if (fps[i] != fps[i-1]) {
	sinfo = myTool.getState(fps[i], sinfo.state);
	if (sinfo == null) {
	  throw new EvalException(EC.TLC_FAILED_TO_RECOVER_NEXT);
	}
	StatePrinter.printState(sinfo, lastState, ++stateNum);
	lastState = sinfo.state;	
      }
    }
    StatePrinter.printStutteringState(++stateNum);
    MP.printMessage(EC.TLC_BACK_TO_STATE, "" + cyclePos);
  }
  
  /**
   * checkSubcomponent checks if a subcomponent satisfies the AEs
   * of the current PEM, and is fulfilling. The subcomponents are
   * those after pruning EAs.  When a counterexample is found, it
   * throws a LiveException exception.
   */
  static void checkSubcomponent(BEGraphNode node) {
    int slen = currentOOS.checkState.length;
    int alen = currentOOS.checkAction.length;
    boolean[] AEStateRes = new boolean[currentPEM.AEState.length];
    boolean[] AEActionRes = new boolean[currentPEM.AEAction.length];
    boolean[] promiseRes = new boolean[currentOOS.promises.length];
    ObjectStack stack = new MemObjectStack(metadir, "subcomstack");

    node.incNumber();
    stack.push(node);
    while (stack.size() != 0) {
      BEGraphNode curNode = (BEGraphNode)stack.pop();
      // Check AEState:
      for (int i = 0; i < currentPEM.AEState.length; i++) {
	if (!AEStateRes[i]) {
	  int idx = currentPEM.AEState[i];
	  AEStateRes[i] = curNode.getCheckState(idx);
	}
      }
      // Check AEAction:
      int nsz = curNode.nextSize();
      for (int i = 0; i < nsz; i++) {
	BEGraphNode node1 = curNode.nextAt(i);
	long num = node1.getNumber();
	if (num >= thirdNum) {
	  for (int j = 0; j < currentPEM.AEAction.length; j++) {
	    if (!AEActionRes[j]) {
	      int idx = currentPEM.AEAction[j];
	      AEActionRes[j] = curNode.getCheckAction(slen, alen, i, idx);
	    }
	  }
	}
	if (num == thirdNum) {
	  node1.incNumber();
	  stack.push(node1);
	}
      }
      // Check that the component is fulfilling. (See MP page 453.)
      // Note that the promises are precomputed and stored in oos.
      for (int i = 0; i < currentOOS.promises.length; i++) {
	LNEven promise = currentOOS.promises[i];
	TBPar par = curNode.getTNode(currentOOS.tableau).getPar();
	if (par.isFulfilling(promise)) {
	  promiseRes[i] = true;
	}
      }
    }
    // Get the number right, so all nodes have numbers < thirdNum.
    thirdNum += 2;

    // We find a counterexample if all three conditions are satisfied.
    for (int i = 0; i < currentPEM.AEState.length; i++) {
      if (!AEStateRes[i]) return;
    }
    for (int i = 0; i < currentPEM.AEAction.length; i++) {
      if (!AEActionRes[i]) return;
    }
    for (int i = 0; i < currentOOS.promises.length; i++) {
      if (!promiseRes[i]) return;
    }
    // This component must contain a counter-example because all three
    // conditions are satisfied. So, print a counter-example!
    try 
    {
        printErrorTrace(node);
    } catch (IOException e) 
    {
        MP.printError(EC.GENERAL, "printing an error trace", e);  // LL changed call 7 April 2012
    }
    throw new LiveException("LiveCheck: Found error trace.");
  }

  /**
   * The method checkSccs finds strongly connected components, and
   * checks the current oos.  We use Tarjan's algorithm described in
   * "Depth-First Search and Linear Graph Algorithms" to compute the
   * strongly connected components.
   */
  static long checkSccs(BEGraphNode node) {
    long lowlink = firstNum++;
    node.setNumber(lowlink);
    comStack.push(node);
    int nsz = node.nextSize();
    for (int i = 0; i < nsz; i++) {
      BEGraphNode destNode = node.nextAt(i);
      long destNum = destNode.getNumber();
      if (destNum == 0) {
	destNum = checkSccs(destNode);
      }
      if (destNum < lowlink) lowlink = destNum;
    }

    if (lowlink == node.getNumber()) {
      // The nodes on the stack from top to node consist of a
      // component. Check it as soon as one is found.
      checkComponent(node);
    }
    return lowlink;
  }

  /* This method checks whether a scc satisfies currentPEM.  */
  static void checkComponent(BEGraphNode node) {
    Vect nodes = extractComponent(node);
    if (nodes != null) {
      PossibleErrorModel[] pems = currentOOS.pems;
      for (int i = 0; i < pems.length; i++) {
	currentPEM = pems[i];
	startSecondNum = secondNum;
	startThirdNum = thirdNum;
	for (int j = nodes.size()-1; j >= 0; j--) {
	  BEGraphNode node1 = (BEGraphNode)nodes.elementAt(j);
	  if (node1.getNumber() < startThirdNum) {
	    checkSccs1(node1);
	  }
	}
	/******
	// Use a special case when there is no EAAction
	if (currentPEM.EAAction == -1) {
	  long thirdTemp = thirdNum;
	  thirdNum = secondNum;
	  checkSubcomponent(node);
	  secondNum = thirdNum;
	  thirdNum = thirdTemp;
	}
	else {
	  startSecondNum = secondNum;
	  startThirdNum = thirdNum;
	  checkSccs1(node);
	}
	******/
      }
    }
  }

  /**
   * Returns the set of nodes in a nontrivial component.  Returns
   * null for a trivial one. It also assigns a new number to all
   * the nodes in the component.
   */
  static Vect extractComponent(BEGraphNode node) {
    BEGraphNode node1 = (BEGraphNode)comStack.pop();
    if (node == node1 && !node.transExists(node)) {
      node.setNumber(MAX_FIRST);
      return null;
    }
    Vect nodes = new Vect();
    numFirstCom = secondNum++;
    numSecondCom = thirdNum;
    node1.setNumber(numFirstCom);
    nodes.addElement(node1);
    while (node != node1) {
      node1 = (BEGraphNode)comStack.pop();
      node1.setNumber(numFirstCom);
      nodes.addElement(node1);      
    }
    return nodes;
  }

  static long checkSccs1(BEGraphNode node) {
    long lowlink = secondNum++;
    node.setNumber(lowlink);
    comStack.push(node);
    int nsz = node.nextSize();
    for (int i = 0; i < nsz; i++) {
      BEGraphNode destNode = node.nextAt(i);
      long destNum = destNode.getNumber();
      if ((numFirstCom <= destNum) &&
	  node.getCheckAction(currentOOS.checkState.length,
			      currentOOS.checkAction.length,
			      i, currentPEM.EAAction)) {
	if ((destNum < startSecondNum) ||
	    (numSecondCom <= destNum && destNum < startThirdNum)) {
	  destNum = checkSccs1(destNode);
	}
	if (destNum < lowlink) lowlink = destNum;
      }
    }
    if (lowlink == node.getNumber()) {
      // The nodes on the stack from top to node consist of a
      // component. Check it as soon as it is found.
      if (extractComponent1(node)) {
	checkSubcomponent(node);
      }
    }
    return lowlink;
  }

  static boolean extractComponent1(BEGraphNode node) {
    BEGraphNode node1 = (BEGraphNode)comStack.pop();
    if (node == node1 && !canStutter(node)) {
      node.setNumber(thirdNum++);
      return false;
    }
    node1.setNumber(thirdNum);
    while (node != node1) {
      node1 = (BEGraphNode)comStack.pop();
      node1.setNumber(thirdNum);
    }
    return true;
  }

  static boolean canStutter(BEGraphNode node) {
    int slen = currentOOS.checkState.length;
    int alen = currentOOS.checkAction.length;

    for (int i = 0; i < node.nextSize(); i++) {
      BEGraphNode node1 = node.nextAt(i);
      if (node.equals(node1)) {
	long nodeNum = node.getNumber();
	return ((numFirstCom <= nodeNum) &&
		node.getCheckAction(slen, alen, i, currentPEM.EAAction));
      }
    }
    return false;
  }
  
}
