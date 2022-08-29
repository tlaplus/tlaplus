// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:44 PST by lamport
//      modified on Fri Jan  4 00:30:06 PST 2002 by yuanyu

package tlc2.tool.liveness;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.StatePrinter;
import tlc2.tool.*;
import tlc2.util.FP64;
import tlc2.util.LongObjTable;
import tlc2.util.SetOfStates;
import tlc2.util.statistics.DummyBucketStatistics;
import tlc2.util.statistics.IBucketStatistics;

import java.util.ArrayList;
import java.util.Objects;
import java.util.Stack;
import java.util.function.Supplier;

public class LiveCheck1 implements ILiveCheck {
    /* The following are the data needed in the scc search. */
    private static final long MAX_FIRST = 0x2000000000000000L;
    private static final long MAX_SECOND = 0x5000000000000000L;
    /**
     * Implementation of liveness checking based on MP book.
     */
    private ITool myTool;
    private String metadir = "";
    private Action[] actions;
    private OrderOfSolution[] solutions;
    private BEGraph[] bgraphs;
    private StateVec stateTrace = null;
    private OrderOfSolution currentOOS = null;
    private PossibleErrorModel currentPEM = null;
    private Stack<BEGraphNode> comStack = null;

    /* firstNum ranges from 1 to MAX_FIRST. */
    private long firstNum = 1;

    /* secondNum ranges from MAX_FIRST+1 to MAX_SECOND. */
    private long secondNum = MAX_FIRST + 1;
    private long startSecondNum = secondNum;

    /* thirdNum ranges from MAX_SECOND+1 to MAX_VALUE. */
    private long thirdNum = MAX_SECOND + 1;
    private long startThirdNum = thirdNum;

    /* The number assigned to a new component found by checkSccs. */
    private long numFirstCom = secondNum;

    /**
     * The starting number assigned to new components found by the many
     * checkSccs1 calls.
     */
    private long numSecondCom = thirdNum;

    /**
     * The initial state used for the current checking. It is used in generating
     * the error trace.
     */
    private BEGraphNode initNode = null;

    public LiveCheck1(final ITool tool) {
        myTool = tool;
        solutions = Liveness.processLiveness(myTool);
        bgraphs = new BEGraph[0];
    }

    public void init(final ITool tool, final Action[] acts, final String mdir) {
        myTool = tool;
        metadir = mdir;
        actions = acts;
        solutions = Liveness.processLiveness(myTool);
        bgraphs = new BEGraph[solutions.length];
        for (int i = 0; i < solutions.length; i++) {
            bgraphs[i] = new BEGraph(metadir, solutions[i].hasTableau());
        }
    }

    /**
     * This method resets the behavior graph so that we can recompute the SCCs.
     */
    @Override
    public void reset() {
        for (final BEGraph bgraph : bgraphs) {
            bgraph.resetNumberField();
        }
    }

    private void initSccParams(final OrderOfSolution os) {
        currentOOS = os;
        comStack = new Stack<>();
        firstNum = 1;
        secondNum = MAX_FIRST + 1;
        thirdNum = MAX_SECOND + 1;
        startSecondNum = secondNum;
        startThirdNum = thirdNum;
        numFirstCom = secondNum;
        numSecondCom = thirdNum;
    }

    /**
     * This method constructs the behavior graph from an OrderOfSolution and a
     * state trace (a sequence of states). Assume trace.length > 0. It returns
     * the set of initial states.
     */
    ArrayList<BEGraphNode> constructBEGraph(final ITool tool, final OrderOfSolution os) {
        final ArrayList<BEGraphNode> initNodes = new ArrayList<>(1);
        final int slen = os.getCheckState().length;
        final int alen = os.getCheckAction().length;
        TLCState srcState = stateTrace.get(0); // the initial state
        final long srcFP = srcState.fingerPrint();
        boolean[] checkStateRes = os.checkState(tool, srcState);
        boolean[] checkActionRes = os.checkAction(tool, srcState, srcState);
        if (!os.hasTableau()) {
            // If there is no tableau, construct begraph with trace.
            final LongObjTable<BEGraphNode> allNodes = new LongObjTable<>(BEGraphNode.class, 127);
            BEGraphNode srcNode = new BEGraphNode(srcFP);
            srcNode.setCheckState(checkStateRes);
            srcNode.addTransition(srcNode, slen, alen, checkActionRes);
            allNodes.put(srcFP, srcNode);
            initNodes.add(srcNode);
            for (int i = 1; i < stateTrace.size(); i++) {
                final TLCState destState = stateTrace.get(i);
                final long destFP = destState.fingerPrint();
                BEGraphNode destNode = allNodes.get(destFP);
                if (destNode == null) {
                    destNode = new BEGraphNode(destFP);
                    destNode.setCheckState(os.checkState(tool, srcState));
                    destNode.addTransition(destNode, slen, alen, os.checkAction(tool, destState, destState));
                    srcNode.addTransition(destNode, slen, alen, os.checkAction(tool, srcState, destState));
                    allNodes.put(destFP, destNode);
                } else if (!srcNode.transExists(destNode)) {
                    srcNode.addTransition(destNode, slen, alen, os.checkAction(tool, srcState, destState));
                }
                srcNode = destNode;
                srcState = destState;
            }
        } else {
            // If there is tableau, construct begraph of (tableau X trace).
            final LongObjTable<BEGraphNode> allNodes = new LongObjTable<>(BEGraphNode.class, 255);
            ArrayList<BEGraphNode> srcNodes = new ArrayList<>();
            final int initCnt = os.getTableau().getInitCnt();
            for (int i = 0; i < initCnt; i++) {
                final TBGraphNode tnode = os.getTableau().getNode(i);
                if (tnode.isConsistent(srcState, myTool)) {
                    final BEGraphNode destNode = new BTGraphNode(srcFP, tnode.getIndex());
                    destNode.setCheckState(checkStateRes);
                    initNodes.add(destNode);
                    srcNodes.add(destNode);
                    allNodes.put(FP64.Extend(srcFP, tnode.getIndex()), destNode);
                }
            }
            for (final BEGraphNode srcNode : srcNodes) {
                final TBGraphNode tnode = srcNode.getTNode(os.getTableau());
                for (int j = 0; j < tnode.nextSize(); j++) {
                    final TBGraphNode tnode1 = tnode.nextAt(j);
                    final long destFP = FP64.Extend(srcFP, tnode1.getIndex());
                    final BEGraphNode destNode = allNodes.get(destFP);
                    if (destNode != null) {
                        srcNode.addTransition(destNode, slen, alen, checkActionRes);
                    }
                }
            }
            for (int i = 1; i < stateTrace.size(); i++) {
                final ArrayList<BEGraphNode> destNodes = new ArrayList<>();
                final TLCState destState = stateTrace.get(i);
                final long destStateFP = destState.fingerPrint();
                checkStateRes = os.checkState(myTool, destState);
                checkActionRes = os.checkAction(tool, srcState, destState);
                for (final BEGraphNode srcNode : srcNodes) {
                    final TBGraphNode tnode = srcNode.getTNode(os.getTableau());
                    for (int k = 0; k < tnode.nextSize(); k++) {
                        final TBGraphNode tnode1 = tnode.nextAt(k);
                        final long destFP = FP64.Extend(destStateFP, tnode1.getIndex());
                        BEGraphNode destNode = allNodes.get(destFP);
                        if (destNode == null) {
                            if (tnode1.isConsistent(destState, myTool)) {
                                destNode = new BTGraphNode(destStateFP, tnode1.getIndex());
                                destNode.setCheckState(checkStateRes);
                                srcNode.addTransition(destNode, slen, alen, checkActionRes);
                                destNodes.add(destNode);
                                allNodes.put(destFP, destNode);
                            }
                        } else if (!srcNode.transExists(destNode)) {
                            srcNode.addTransition(destNode, slen, alen, checkActionRes);
                        }
                    }
                }
                checkActionRes = os.checkAction(tool, destState, destState);
                for (int j = 0; j < destNodes.size(); j++) {
                    final BEGraphNode srcNode = destNodes.get(j);
                    final TBGraphNode tnode = srcNode.getTNode(os.getTableau());
                    for (int k = 0; k < tnode.nextSize(); k++) {
                        final TBGraphNode tnode1 = tnode.nextAt(k);
                        final long destFP = FP64.Extend(destStateFP, tnode1.getIndex());
                        BEGraphNode destNode = allNodes.get(destFP);
                        if (destNode == null) {
                            if (tnode1.isConsistent(destState, myTool)) {
                                destNode = new BTGraphNode(destStateFP, tnode1.getIndex());
                                destNode.setCheckState(checkStateRes);
                                srcNode.addTransition(destNode, slen, alen, checkActionRes);
                                destNodes.add(destNode);
                                allNodes.put(destFP, destNode);
                            }
                        } else if (!srcNode.transExists(destNode)) {
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
     * This method adds new nodes into the behavior graph when a new initial
     * state is generated.
     */
    @Override
    public void addInitState(final ITool tool, final TLCState state, final long stateFP) {
        for (int soln = 0; soln < solutions.length; soln++) {
            final OrderOfSolution os = solutions[soln];
            final BEGraph bgraph = bgraphs[soln];
            final int slen = os.getCheckState().length;
            final int alen = os.getCheckAction().length;
            final boolean[] checkStateRes = os.checkState(tool, state);
            final boolean[] checkActionRes = os.checkAction(tool, state, state);
            // Adding nodes and transitions:
            if (!os.hasTableau()) {
                // if there is no tableau ...
                final BEGraphNode node = new BEGraphNode(stateFP);
                node.setCheckState(checkStateRes);
                bgraph.addInitNode(node);
                node.addTransition(node, slen, alen, checkActionRes);
                bgraph.allNodes.putBENode(node);
            } else {
                // if there is tableau ...
                // Add edges induced by root --> state:
                final int initCnt = os.getTableau().getInitCnt();
                for (int i = 0; i < initCnt; i++) {
                    final TBGraphNode tnode = os.getTableau().getNode(i);
                    if (tnode.isConsistent(state, myTool)) {
                        final BTGraphNode destNode = new BTGraphNode(stateFP, tnode.getIndex());
                        destNode.setCheckState(checkStateRes);
                        bgraph.addInitNode(destNode);
                        bgraph.allNodes.putBTNode(destNode);
                        // Add edges induced by state --> state:
                        addNodesForStut(state, stateFP, destNode, checkStateRes, checkActionRes, os, bgraph);
                    }
                }
            }
            // we are done with this state:
            bgraph.allNodes.setDone(stateFP);
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#addNextState(tlc2.tool.TLCState, long, tlc2.util.SetOfStates)
     */
    @Override
    public void addNextState(final ITool tool, final TLCState s0, final long fp0, final SetOfStates nextStates) {
        for (final TLCState s2 : nextStates) {
            final long fp2 = s2.fingerPrint();
            addNextState(tool, s0, fp0, s2, fp2);
        }
    }

    /**
     * This method adds new nodes into the behavior graph when a new state is
     * generated. The argument s2 is the new state. The argument s1 is parent
     * state of s2.
     */
    public synchronized void addNextState(final ITool tool, final TLCState s1, final long fp1, final TLCState s2, final long fp2) {
        for (int soln = 0; soln < solutions.length; soln++) {
            final OrderOfSolution os = solutions[soln];
            final BEGraph bgraph = bgraphs[soln];
            final int slen = os.getCheckState().length;
            final int alen = os.getCheckAction().length;
            // Adding node and transitions:
            if (!os.hasTableau()) {
                // if there is no tableau ...
                final BEGraphNode node1 = bgraph.allNodes.getBENode(fp1);
                BEGraphNode node2 = bgraph.allNodes.getBENode(fp2);
                if (node2 == null) {
                    node2 = new BEGraphNode(fp2);
                    node2.setCheckState(os.checkState(tool, s2));
                    Objects.requireNonNull(node1).addTransition(node2, slen, alen, os.checkAction(tool, s1, s2));
                    node2.addTransition(node2, slen, alen, os.checkAction(tool, s2, s2));
                    bgraph.allNodes.putBENode(node2);
                } else if (!Objects.requireNonNull(node1).transExists(node2)) {
                    final boolean[] checkActionRes = os.checkAction(tool, s1, s2);
                    node1.addTransition(node2, slen, alen, checkActionRes);
                }
            } else {
                // if there is tableau ...
                final BTGraphNode[] srcNodes = bgraph.allNodes.getBTNode(fp1);
                if (srcNodes == null) {
                    continue; // nothing to add
                }
                boolean[] checkStateRes = null;
                // Add edges induced by s1 --> s2:
                final boolean[] checkActionRes = os.checkAction(tool, s1, s2);
                boolean[] checkActionRes1 = null;
                for (final BTGraphNode srcNode : srcNodes) {
                    final TBGraphNode tnode = os.getTableau().getNode(srcNode.getIndex());
                    for (int j = 0; j < tnode.nextSize(); j++) {
                        final TBGraphNode tnode1 = tnode.nextAt(j);
                        BTGraphNode destNode = bgraph.allNodes.getBTNode(fp2, tnode1.getIndex());
                        if (destNode == null) {
                            if (tnode1.isConsistent(s2, myTool)) {
                                destNode = new BTGraphNode(fp2, tnode1.getIndex());
                                if (checkStateRes == null) {
                                    checkStateRes = os.checkState(tool, s2);
                                }
                                destNode.setCheckState(checkStateRes);
                                srcNode.addTransition(destNode, slen, alen, checkActionRes);
                                final int idx = bgraph.allNodes.putBTNode(destNode);
                                // add edges induced by s2 --> s2:
                                if (checkActionRes1 == null) {
                                    checkActionRes1 = os.checkAction(tool, s2, s2);
                                }
                                addNodesForStut(s2, fp2, destNode, checkStateRes, checkActionRes1, os, bgraph);
                                // if s2 is done, we have to do something for
                                // destNode:
                                if (bgraph.allNodes.isDone(idx)) {
                                    addNextState(tool, s2, fp2, destNode, os, bgraph);
                                }
                            }
                        } else if (!srcNode.transExists(destNode)) {
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
    private void addNodesForStut(final TLCState state, final long fp, final BTGraphNode node, final boolean[] checkState,
                                 final boolean[] checkAction, final OrderOfSolution os, final BEGraph bgraph) {
        final int slen = os.getCheckState().length;
        final int alen = os.getCheckAction().length;
        final TBGraphNode tnode = node.getTNode(os.getTableau());
        for (int i = 0; i < tnode.nextSize(); i++) {
            final TBGraphNode tnode1 = tnode.nextAt(i);
            BTGraphNode destNode = bgraph.allNodes.getBTNode(fp, tnode1.getIndex());
            if (destNode == null) {
                if (tnode1.isConsistent(state, myTool)) {
                    destNode = new BTGraphNode(fp, tnode1.getIndex());
                    destNode.setCheckState(checkState);
                    node.addTransition(destNode, slen, alen, checkAction);
                    bgraph.allNodes.putBTNode(destNode);
                    addNodesForStut(state, fp, destNode, checkState, checkAction, os, bgraph);
                }
            } else {
                node.addTransition(destNode, slen, alen, checkAction);
            }
        }
    }

    /**
     * This method takes care of the case that a new node (s, t) is generated
     * after s has been done. So, we still have to compute the children of (s,
     * t). Hopefully, this case will not occur very frequently.
     */
    private void addNextState(final ITool tool, final TLCState s, final long fp, final BTGraphNode node, final OrderOfSolution os, final BEGraph bgraph) {
        final TBGraphNode tnode = node.getTNode(os.getTableau());
        final int slen = os.getCheckState().length;
        final int alen = os.getCheckAction().length;
        boolean[] checkStateRes = null;
        boolean[] checkActionRes = null;
        for (final Action curAction : actions) {
            final StateVec nextStates = myTool.getNextStates(curAction, s);
            for (final TLCState s1 : nextStates) {
                // Add edges induced by s -> s1:
                final long fp1 = s1.fingerPrint();
                boolean[] checkActionRes1 = null;
                for (int k = 0; k < tnode.nextSize(); k++) {
                    final TBGraphNode tnode1 = tnode.nextAt(k);
                    BTGraphNode destNode = bgraph.allNodes.getBTNode(fp1, tnode1.getIndex());
                    if (destNode == null) {
                        if (tnode1.isConsistent(s1, myTool)) {
                            destNode = new BTGraphNode(fp1, tnode1.getIndex());
                            if (checkStateRes == null) {
                                checkStateRes = os.checkState(tool, s1);
                            }
                            if (checkActionRes == null) {
                                checkActionRes = os.checkAction(tool, s, s1);
                            }
                            destNode.setCheckState(checkStateRes);
                            node.addTransition(destNode, slen, alen, checkActionRes);
                            if (checkActionRes1 == null) {
                                checkActionRes1 = os.checkAction(tool, s1, s1);
                            }
                            addNodesForStut(s1, fp1, destNode, checkStateRes, checkActionRes1, os, bgraph);
                            final int idx = bgraph.allNodes.putBTNode(destNode);
                            if (bgraph.allNodes.isDone(idx)) {
                                addNextState(tool, s1, fp1, destNode, os, bgraph);
                            }
                        }
                    } else if (!node.transExists(destNode)) {
                        if (checkActionRes == null) {
                            checkActionRes = os.checkAction(tool, s, s1);
                        }
                        node.addTransition(destNode, slen, alen, checkActionRes);
                    }
                }
            }
        }
    }

    public synchronized void setDone(final long fp) {
        for (int soln = 0; soln < solutions.length; soln++) {
            bgraphs[soln].allNodes.setDone(fp);
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#doLiveCheck()
     */
    @Override
    public boolean doLiveCheck() {
        return true;
    }

    /**
     * Checks if the partial behavior graph constructed up to now contains any
     * "bad" cycle. A "bad" cycle gives rise to a violation of liveness
     * property.
     */
    @Override
    public synchronized int check(final ITool tool, final boolean forceCheck) {
        final int slen = solutions.length;
        if (slen == 0) {
            return EC.NO_ERROR;
        }

        for (int soln = 0; soln < slen; soln++) {
            final OrderOfSolution oos = solutions[soln];

            // Liveness.printTBGraph(oos.tableau);
            // ToolIO.err.println(bgraphs[soln].toString());

            // We now compute the SCCs of the graph. If we find any SCC
            // that is fulfilling and satisfies any of PEM's, then that
            // SCC contains a "bad" cycle.
            initSccParams(oos);
            final BEGraph bgraph = bgraphs[soln];
            final int numOfInits = bgraph.initSize();
            for (int i = 0; i < numOfInits; i++) {
                initNode = bgraph.getInitNode(i);
                if (initNode.getNumber() == 0) {
                    checkSccs(initNode);
                }
            }
        }
        // Previous for loop with throw LivenessException anyway, thus no harm
        // returning true regardless.
        return EC.NO_ERROR;
    }

    /**
     * Checks if the behavior graph constructed from a state trace contains any
     * "bad" cycle.
     */
    @Override
    public synchronized void checkTrace(final ITool tool, final Supplier<StateVec> trace) {
        stateTrace = trace.get();
        for (final OrderOfSolution os : solutions) {
            final ArrayList<BEGraphNode> initNodes = constructBEGraph(tool, os);

            // Liveness.printTBGraph(os.tableau);
            // ToolIO.err.println(os.behavior.toString());

            // We now compute the SCCs of the graph. If we find any SCC
            // that is fulfilling and satisfies any of PEM's, then that
            // SCC contains a "bad" cycle.
            initSccParams(os);
            final int numOfInits = initNodes.size();
            for (BEGraphNode node : initNodes) {
                initNode = node;
                if (initNode.getNumber() == 0) {
                    checkSccs(initNode);
                }
            }
        }
    }

    /* Print out the error state trace. */
    void printErrorTrace(final BEGraphNode node) {
        MP.printError(EC.TLC_TEMPORAL_PROPERTY_VIOLATED);
        MP.printError(EC.TLC_COUNTER_EXAMPLE);
        // First, find a "bad" cycle from the "bad" scc.
        final Stack<BEGraphNode> cycleStack = new Stack<>();
        final int slen = currentOOS.getCheckState().length;
        final int alen = currentOOS.getCheckAction().length;
        final long lowNum = thirdNum - 1;
        final boolean[] AEStateRes = new boolean[currentPEM.AEState.length];
        final boolean[] AEActionRes = new boolean[currentPEM.AEAction.length];
        final boolean[] promiseRes = new boolean[currentOOS.getPromises().length];
        int cnt = AEStateRes.length + AEActionRes.length + promiseRes.length;
        BEGraphNode curNode = node;
        while (cnt > 0) {
            curNode.setNumber(thirdNum);
            final int cnt0 = cnt;
            _next:
            while (true) {
                // Check AEState:
                for (int i = 0; i < currentPEM.AEState.length; i++) {
                    final int idx = currentPEM.AEState[i];
                    if (!AEStateRes[i] && curNode.getCheckState(idx)) {
                        AEStateRes[i] = true;
                        cnt--;
                    }
                }
                // Check if the component is fulfilling. (See MP page 453.)
                // Note that the promises are precomputed and stored in oos.
                for (int i = 0; i < currentOOS.getPromises().length; i++) {
                    final LNEven promise = currentOOS.getPromises()[i];
                    final TBPar par = curNode.getTNode(currentOOS.getTableau()).getPar();
                    if (!promiseRes[i] && par.isFulfilling(promise)) {
                        promiseRes[i] = true;
                        cnt--;
                    }
                }
                if (cnt <= 0) {
                    break;
                }
                // Check AEAction:
                BEGraphNode nextNode1 = null;
                BEGraphNode nextNode2 = null;
                final int cnt1 = cnt;
                for (int i = 0; i < curNode.nextSize(); i++) {
                    final BEGraphNode node1 = curNode.nextAt(i);
                    final long num = node1.getNumber();
                    if (lowNum <= num && num <= thirdNum) {
                        nextNode1 = node1;
                        for (int j = 0; j < currentPEM.AEAction.length; j++) {
                            final int idx = currentPEM.AEAction[j];
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
                    if (lowNum <= num && num < thirdNum) {
                        nextNode2 = node1;
                    }
                }
                if (cnt < cnt0) {
                    cycleStack.push(curNode);
                    curNode = nextNode1;
                    thirdNum++;
                    break;
                }
                // Backtrack if needed:
                while (nextNode2 == null) {
                    curNode = cycleStack.pop();
                    for (int i = 0; i < Objects.requireNonNull(curNode).nextSize(); i++) {
                        final BEGraphNode node1 = curNode.nextAt(i);
                        final long num = node1.getNumber();
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
        // Close the path to form a cycle. curNode has not been pushed on
        // cycleStack.
        curNode.setNumber(++thirdNum);
        _done:
        while (curNode != node) {
            boolean found = false;
            for (int i = 0; i < Objects.requireNonNull(curNode).nextSize(); i++) {
                final BEGraphNode nextNode = curNode.nextAt(i);
                final long num = nextNode.getNumber();
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
                curNode = cycleStack.pop();
            }
        }
        if (cycleStack.size() == 0) {
            cycleStack.push(curNode);
        }

        // Now, print the error trace. We first construct the prefix that
        // led to the bad cycle. The nodes on prefix and cycleStack then
        // form the complete counter example.
        int stateNum = 0;
        final BEGraphNode[] prefix = BEGraph.getPath(initNode, node);
        final TLCStateInfo[] states = new TLCStateInfo[prefix.length];

        // Recover the initial state:
        long fp = prefix[0].stateFP;
        TLCStateInfo sinfo = myTool.getState(fp);
        if (sinfo == null) {
            throw new EvalException(EC.TLC_FAILED_TO_RECOVER_INIT);
        }
        states[stateNum++] = sinfo;

        // Recover the successor states:
        for (int i = 1; i < states.length; i++) {
            final long fp1 = prefix[i].stateFP;
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
        TLCState cycleState = null;
        for (int i = 0; i < stateNum; i++) {
            StatePrinter.printInvariantViolationStateTraceState(states[i], cycleState, i + 1);
            cycleState = states[i].state;
        }

        // Print the cycle:
        TLCState lastState = cycleState;
        final int cyclePos = stateNum;
        final long[] fps = new long[cycleStack.size()];
        int idx = fps.length;
        while (idx > 0) {
            fps[--idx] = Objects.requireNonNull(cycleStack.pop()).stateFP;
        }
        // Assert.assert(fps.length > 0);
        sinfo = states[stateNum - 1];
        for (int i = 1; i < fps.length; i++) {
            if (fps[i] != fps[i - 1]) {
                sinfo = myTool.getState(fps[i], sinfo.state);
                if (sinfo == null) {
                    throw new EvalException(EC.TLC_FAILED_TO_RECOVER_NEXT);
                }
                StatePrinter.printInvariantViolationStateTraceState(sinfo, lastState, ++stateNum);
                lastState = sinfo.state;
            }
        }
        if (node.stateFP == lastState.fingerPrint()) {
            StatePrinter.printStutteringState(stateNum);
        } else {
            sinfo = myTool.getState(cycleState.fingerPrint(), sinfo);
            // The print stmts below claim there is a cycle, thus assert that
            // there is indeed one. Index-based lookup into states array is
            // reduced by one because cyclePos is human-readable.
            assert cycleState.equals(sinfo.state);
            StatePrinter.printBackToState(sinfo, cyclePos);
        }
    }

    /**
     * checkSubcomponent checks if a subcomponent satisfies the AEs of the
     * current PEM, and is fulfilling. The subcomponents are those after pruning
     * EAs. When a counterexample is found, it throws a LiveException exception.
     */
    void checkSubcomponent(final BEGraphNode node) {
        final int slen = currentOOS.getCheckState().length;
        final int alen = currentOOS.getCheckAction().length;
        final boolean[] AEStateRes = new boolean[currentPEM.AEState.length];
        final boolean[] AEActionRes = new boolean[currentPEM.AEAction.length];
        final boolean[] promiseRes = new boolean[currentOOS.getPromises().length];
        final Stack<BEGraphNode> stack = new Stack<>();

        node.incNumber();
        stack.push(node);
        while (stack.size() != 0) {
            final BEGraphNode curNode = stack.pop();
            // Check AEState:
            for (int i = 0; i < currentPEM.AEState.length; i++) {
                if (!AEStateRes[i]) {
                    final int idx = currentPEM.AEState[i];
                    AEStateRes[i] = Objects.requireNonNull(curNode).getCheckState(idx);
                }
            }
            // Check AEAction:
            final int nsz = Objects.requireNonNull(curNode).nextSize();
            for (int i = 0; i < nsz; i++) {
                final BEGraphNode node1 = curNode.nextAt(i);
                final long num = node1.getNumber();
                if (num >= thirdNum) {
                    for (int j = 0; j < currentPEM.AEAction.length; j++) {
                        if (!AEActionRes[j]) {
                            final int idx = currentPEM.AEAction[j];
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
            for (int i = 0; i < currentOOS.getPromises().length; i++) {
                final LNEven promise = currentOOS.getPromises()[i];
                final TBPar par = curNode.getTNode(currentOOS.getTableau()).getPar();
                if (par.isFulfilling(promise)) {
                    promiseRes[i] = true;
                }
            }
        }
        // Get the number right, so all nodes have numbers < thirdNum.
        thirdNum += 2;

        // We find a counterexample if all three conditions are satisfied.
        for (int i = 0; i < currentPEM.AEState.length; i++) {
            if (!AEStateRes[i]) {
                return;
            }
        }
        for (int i = 0; i < currentPEM.AEAction.length; i++) {
            if (!AEActionRes[i]) {
                return;
            }
        }
        for (int i = 0; i < currentOOS.getPromises().length; i++) {
            if (!promiseRes[i]) {
                return;
            }
        }
        // This component must contain a counter-example because all three
        // conditions are satisfied. So, print a counter-example!
        printErrorTrace(node);

        throw new LiveException(EC.TLC_TEMPORAL_PROPERTY_VIOLATED, "LiveCheck: Found error trace.");
    }

    /**
     * The method checkSccs finds strongly connected components, and checks the
     * current oos. We use Tarjan's algorithm described in
     * "Depth-First Search and Linear Graph Algorithms" to compute the strongly
     * connected components.
     */
    long checkSccs(final BEGraphNode node) {
        long lowlink = firstNum++;
        node.setNumber(lowlink);
        comStack.push(node);
        final int nsz = node.nextSize();
        for (int i = 0; i < nsz; i++) {
            final BEGraphNode destNode = node.nextAt(i);
            long destNum = destNode.getNumber();
            if (destNum == 0) {
                destNum = checkSccs(destNode);
            }
            if (destNum < lowlink) {
                lowlink = destNum;
            }
        }

        if (lowlink == node.getNumber()) {
            // The nodes on the stack from top to node consist of a
            // component. Check it as soon as one is found.
            checkComponent(node);
        }
        return lowlink;
    }

    /* This method checks whether a scc satisfies currentPEM. */
    void checkComponent(final BEGraphNode node) {
        final ArrayList<BEGraphNode> nodes = extractComponent(node);
        if (nodes != null) {
            final PossibleErrorModel[] pems = currentOOS.getPems();
            /******
             * // Use a special case when there is no EAAction if
             * (currentPEM.EAAction == -1) { long thirdTemp = thirdNum;
             * thirdNum = secondNum; checkSubcomponent(node); secondNum =
             * thirdNum; thirdNum = thirdTemp; } else { startSecondNum =
             * secondNum; startThirdNum = thirdNum; checkSccs1(node); }
             ******/
            for (final PossibleErrorModel pem : pems) {
                currentPEM = pem;
                startSecondNum = secondNum;
                startThirdNum = thirdNum;
                for (int j = nodes.size() - 1; j >= 0; j--) {
                    final BEGraphNode node1 = nodes.get(j);
                    if (node1.getNumber() < startThirdNum) {
                        checkSccs1(node1);
                    }
                }
                /******
                 * // Use a special case when there is no EAAction if
                 * (currentPEM.EAAction == -1) { long thirdTemp = thirdNum;
                 * thirdNum = secondNum; checkSubcomponent(node); secondNum =
                 * thirdNum; thirdNum = thirdTemp; } else { startSecondNum =
                 * secondNum; startThirdNum = thirdNum; checkSccs1(node); }
                 ******/
            }
        }
    }

    /**
     * Returns the set of nodes in a nontrivial component. Returns null for a
     * trivial one. It also assigns a new number to all the nodes in the
     * component.
     */
    ArrayList<BEGraphNode> extractComponent(final BEGraphNode node) {
        BEGraphNode node1 = comStack.pop();
        if (node == node1 && !node.transExists(node)) {
            node.setNumber(MAX_FIRST);
            return null;
        }
        final ArrayList<BEGraphNode> nodes = new ArrayList<>();
        numFirstCom = secondNum++;
        numSecondCom = thirdNum;
        Objects.requireNonNull(node1).setNumber(numFirstCom);
        nodes.add(node1);
        while (node != node1) {
            node1 = comStack.pop();
            Objects.requireNonNull(node1).setNumber(numFirstCom);
            nodes.add(node1);
        }
        return nodes;
    }

    long checkSccs1(final BEGraphNode node) {
        long lowlink = secondNum++;
        node.setNumber(lowlink);
        comStack.push(node);
        final int nsz = node.nextSize();
        for (int i = 0; i < nsz; i++) {
            final BEGraphNode destNode = node.nextAt(i);
            long destNum = destNode.getNumber();
            if ((numFirstCom <= destNum)
                    && node.getCheckAction(currentOOS.getCheckState().length, currentOOS.getCheckAction().length, i,
                    currentPEM.EAAction)) {
                if ((destNum < startSecondNum) || (numSecondCom <= destNum && destNum < startThirdNum)) {
                    destNum = checkSccs1(destNode);
                }
                if (destNum < lowlink) {
                    lowlink = destNum;
                }
            }
        }
        if (lowlink == node.getNumber() && extractComponent1(node)) {
            // The nodes on the stack from top to node consist of a
            // component. Check it as soon as it is found.

            checkSubcomponent(node);
        }
        return lowlink;
    }

    boolean extractComponent1(final BEGraphNode node) {
        BEGraphNode node1 = comStack.pop();
        if (node == node1 && !canStutter(node)) {
            node.setNumber(thirdNum++);
            return false;
        }
        Objects.requireNonNull(node1).setNumber(thirdNum);
        while (node != node1) {
            node1 = comStack.pop();
            Objects.requireNonNull(node1).setNumber(thirdNum);
        }
        return true;
    }

    boolean canStutter(final BEGraphNode node) {
        final int slen = currentOOS.getCheckState().length;
        final int alen = currentOOS.getCheckAction().length;

        for (int i = 0; i < node.nextSize(); i++) {
            final BEGraphNode node1 = node.nextAt(i);
            if (node.equals(node1)) {
                final long nodeNum = node.getNumber();
                return ((numFirstCom <= nodeNum) && node.getCheckAction(slen, alen, i, currentPEM.EAAction));
            }
        }
        return false;
    }

    @Override
    public int finalCheck(final ITool tool) {
        return check(tool, true);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#getMetaDir()
     */
    @Override
    public String getMetaDir() {
        return metadir;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#getTool()
     */
    public ITool getTool() {
        return myTool;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#getOutDegreeStatistics()
     */
    @Override
    public IBucketStatistics getOutDegreeStatistics() {
        return new DummyBucketStatistics();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#getChecker(int)
     */
    @Override
    public ILiveChecker getChecker(final int idx) {
        return null;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#getNumChecker()
     */
    @Override
    public int getNumChecker() {
        return 0;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#close()
     */
    @Override
    public void close() {
        // Intentional no op - LiveCheck1 has no disk files.
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#beginChkpt()
     */
    @Override
    public void beginChkpt() {
        // Intentional no op - LiveCheck1 has no disk files.
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#commitChkpt()
     */
    @Override
    public void commitChkpt() {
        // Intentional no op - LiveCheck1 has no disk files.
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#recover()
     */
    @Override
    public void recover() {
        // Intentional no op - LiveCheck1 has no disk files.
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#calculateInDegreeDiskGraphs(tlc2.util.statistics.IBucketStatistics)
     */
    @Override
    public IBucketStatistics calculateInDegreeDiskGraphs(final IBucketStatistics aGraphStats) {
        return new DummyBucketStatistics();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.ILiveCheck#calculateOutDegreeDiskGraphs(tlc2.util.statistics.IBucketStatistics)
     */
    @Override
    public IBucketStatistics calculateOutDegreeDiskGraphs(final IBucketStatistics aGraphStats) {
        return new DummyBucketStatistics();
    }

}
