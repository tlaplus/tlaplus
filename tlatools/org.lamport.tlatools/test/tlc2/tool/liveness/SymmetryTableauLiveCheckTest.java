/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package tlc2.tool.liveness;

import org.easymock.Capture;
import org.easymock.EasyMock;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import tlc2.tool.Action;
import tlc2.tool.ITool;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.liveness.GraphNode.Transition;
import tlc2.tool.queue.DummyTLCState;
import tlc2.util.SetOfStates;
import tlc2.util.statistics.DummyBucketStatistics;

import java.util.BitSet;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class SymmetryTableauLiveCheckTest {

    private ITool tool;

    @Before
    public void createTool() {
        this.tool = EasyMock.createNiceMock(ITool.class);
    }

    @Test
    @Ignore("Ignored for as long as symmetry is incorrectly handled by TLC with liveness checking.")
    public void testTableau() throws Exception {
        final ILiveCheck lc = getLiveCheckWithTwoNodeTableau();

        final SetOfStates nexts = new SetOfStates(1);
        final AbstractDiskGraph diskGraph = lc.getChecker(0).getDiskGraph();

        // Add init state v
        final TLCState v = new DummyTLCState(tool.getVariables(), 100L);
        lc.addInitState(tool, v, v.fingerPrint());

        // one init node (two elements in LongVec)
        assertEquals(1, diskGraph.getInitNodes().size() / 2);

        // Add v > s
        final TLCState s = new DummyTLCState(tool.getVariables(), 200L);
        nexts.add(s);
        lc.addNextState(null, v, v.fingerPrint(), nexts);

        assertEquals(2, diskGraph.getNode(v.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(v.fingerPrint(), 1).succSize()); // only tidx0 is an init node

        assertEquals(0, diskGraph.getNode(s.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(s.fingerPrint(), 1).succSize());

        // Add s > t
        nexts.clear();
        final TLCState t = new DummyTLCState(tool.getVariables(), 300L);
        nexts.add(t);
        lc.addNextState(null, s, s.fingerPrint(), nexts);

        assertEquals(2, diskGraph.getNode(v.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(v.fingerPrint(), 1).succSize());

        assertEquals(2, diskGraph.getNode(s.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(s.fingerPrint(), 1).succSize());

        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 1).succSize());

        // add s > u
        nexts.clear();
        final TLCState u = new DummyTLCState(tool.getVariables(), 400L);
        nexts.add(u);
        lc.addNextState(null, s, s.fingerPrint(), nexts);

        Assert.fail("finish incomplete test! Assertions below are partially bogus.");

        assertEquals(2, diskGraph.getNode(v.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(v.fingerPrint(), 1).succSize());

        assertEquals(4, diskGraph.getNode(s.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(s.fingerPrint(), 1).succSize());

        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 1).succSize());

        assertEquals(0, diskGraph.getNode(u.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(u.fingerPrint(), 1).succSize());

        assertTrue(diskGraph.checkInvariants(0, 0));

        lc.close();
    }

    private ILiveCheck getLiveCheckWithTwoNodeTableau() throws Exception {
        final TBGraphNode node1 = EasyMock.createNiceMock(TBGraphNode.class);
        EasyMock.expect(node1.isConsistent(EasyMock.anyObject(), EasyMock.anyObject()))
                .andReturn(true).anyTimes();
        EasyMock.expect(node1.nextSize()).andReturn(0).anyTimes();
        EasyMock.expect(node1.getIndex()).andReturn(1).anyTimes();
        EasyMock.replay(node1);

        final TBGraphNode node0 = EasyMock.createMock(TBGraphNode.class);
        EasyMock.expect(node0.isConsistent(EasyMock.anyObject(), EasyMock.anyObject()))
                .andReturn(true).anyTimes();
        EasyMock.expect(node0.nextSize()).andReturn(2).anyTimes();
        EasyMock.expect(node0.nextAt(0)).andReturn(node0).anyTimes();
        EasyMock.expect(node0.nextAt(1)).andReturn(node1).anyTimes();
        EasyMock.expect(node0.getIndex()).andReturn(0).anyTimes();
        EasyMock.replay(node0);

        final TBGraph tbGraph = new TBGraph();
        tbGraph.add(node0);
        tbGraph.add(node1);
        tbGraph.setInitCnt(1);

        // Configure OOS mock to react to the subsequent invocation. This is a
        // essentially the list of calls being made on OOS during
        // LiveCheck#addInitState and LiveCheck#addNextState
        final OrderOfSolution oos = EasyMock.createNiceMock(OrderOfSolution.class);
        EasyMock.expect(oos.hasTableau()).andReturn(true);
        EasyMock.expect(oos.getTableau()).andReturn(tbGraph).anyTimes();
        EasyMock.expect(oos.getCheckAction()).andReturn(new LiveExprNode[0]).anyTimes();
        EasyMock.expect(oos.getCheckState()).andReturn(new LiveExprNode[0]).anyTimes();
        EasyMock.expect(oos.checkState(null, EasyMock.anyObject())).andReturn(new boolean[0]).anyTimes();
        EasyMock.replay(oos);

        return new LiveCheck(tool,
                new OrderOfSolution[]{oos}, System.getProperty("java.io.tmpdir"), new DummyBucketStatistics(), null);
    }

    @Test
    @Ignore("Ignored for as long as symmetry is incorrectly handled by TLC with liveness checking.")
    public void testSymmetry() throws Exception {
        final TLCState s = new DummyTLCState(tool.getVariables(), 200L);
        final TLCState s1 = new DummyTLCState(tool.getVariables(), s.fingerPrint()); // symmetric sibling of s
        final TLCState t = new DummyTLCState(tool.getVariables(), 300L);

        final ILiveCheck lc = getLiveCheckWithTwoNodeTableauSymmetry(s, s1, t);

        final SetOfStates nexts = new SetOfStates(1);
        final AbstractDiskGraph diskGraph = lc.getChecker(0).getDiskGraph();

        // Add init state v
        final TLCState v = new DummyTLCState(tool.getVariables(), 100L);
        lc.addInitState(tool, v, v.fingerPrint());

        // one init node (two elements in LongVec)
        assertEquals(1, diskGraph.getInitNodes().size() / 2);

        // Add v > s
        nexts.add(s);
        lc.addNextState(null, v, v.fingerPrint(), nexts);

        final GraphNode vgn = diskGraph.getNode(v.fingerPrint(), 0);
        assertEquals(2, vgn.succSize()); // s is consistent with tidx0 and tidx1, but not with tidx2
        final Set<Transition> tvgn = vgn.getTransition();
        assertTrue(tvgn.contains(new Transition(s.fingerPrint(), 0, new BitSet(0))));
        assertTrue(tvgn.contains(new Transition(s.fingerPrint(), 1, new BitSet(0))));
        assertEquals(0, diskGraph.getNode(v.fingerPrint(), 1).succSize()); // only tidx0 is an init node
        assertEquals(0, diskGraph.getNode(v.fingerPrint(), 2).succSize()); // only tidx0 is an init node

        assertEquals(0, diskGraph.getNode(s.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(s.fingerPrint(), 1).succSize());
        assertEquals(0, diskGraph.getNode(s.fingerPrint(), 2).succSize());

        // Add s > t
        nexts.clear();
        nexts.add(t);
        lc.addNextState(null, s, s.fingerPrint(), nexts);

        assertEquals(2, diskGraph.getNode(v.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(v.fingerPrint(), 1).succSize());
        assertEquals(0, diskGraph.getNode(v.fingerPrint(), 2).succSize());

        // Even though t is consistent with all three tableau nodes (0,1,2),
        // (fingerprint X tableau idx) node <<200.0>> checks only its direct
        // succeccors tidx0, tidx1. Not tidx2;
        assertEquals(2, diskGraph.getNode(s.fingerPrint(), 0).succSize()); // 300.0, 300.1
        // <<200,1>> checks tidx1 and tidx2
        assertEquals(2, diskGraph.getNode(s.fingerPrint(), 1).succSize()); // 300.1, 300.2
        assertEquals(0, diskGraph.getNode(s.fingerPrint(), 2).succSize());

        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 1).succSize());
        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 2).succSize());

        // Add additional init state u
        final TLCState u = new DummyTLCState(tool.getVariables(), 400L);
        lc.addInitState(tool, u, u.fingerPrint());

        // two init nodes now (four elements in LongVec)
        assertEquals(2, diskGraph.getInitNodes().size() / 2);

        assertEquals(2, diskGraph.getNode(v.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(v.fingerPrint(), 1).succSize());
        assertEquals(0, diskGraph.getNode(v.fingerPrint(), 2).succSize());

        assertEquals(2, diskGraph.getNode(s.fingerPrint(), 0).succSize());
        assertEquals(2, diskGraph.getNode(s.fingerPrint(), 1).succSize());
        assertEquals(0, diskGraph.getNode(s.fingerPrint(), 2).succSize());

        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 1).succSize());
        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 2).succSize());

        assertEquals(0, diskGraph.getNode(u.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(u.fingerPrint(), 1).succSize());
        assertEquals(0, diskGraph.getNode(u.fingerPrint(), 2).succSize());

        // add a symmetric s1 (same fingerprint as s)
        nexts.clear();
        nexts.add(s1);
        lc.addNextState(null, u, u.fingerPrint(), nexts);

        assertEquals(2, diskGraph.getNode(v.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(v.fingerPrint(), 1).succSize());
        assertEquals(0, diskGraph.getNode(v.fingerPrint(), 2).succSize());

        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 1).succSize());
        assertEquals(0, diskGraph.getNode(t.fingerPrint(), 2).succSize());

        assertEquals(1, diskGraph.getNode(u.fingerPrint(), 0).succSize());
        assertEquals(0, diskGraph.getNode(u.fingerPrint(), 1).succSize());
        assertEquals(0, diskGraph.getNode(u.fingerPrint(), 2).succSize());

        Assert.fail("finish incomplete test! Assertions below are partially bogus.");

        //TODO GN are equals in terms of <<state, tidx>> but not necessarily transitions
        assertEquals(diskGraph.getNode(s1.fingerPrint(), 0), diskGraph.getNode(s.fingerPrint(), 0));
        assertEquals(diskGraph.getNode(s1.fingerPrint(), 1), diskGraph.getNode(s.fingerPrint(), 1));
        assertEquals(diskGraph.getNode(s1.fingerPrint(), 2), diskGraph.getNode(s.fingerPrint(), 2));

        // s1 and s are represented by the same GraphNode
        final GraphNode node200_0 = diskGraph.getNode(s.fingerPrint(), 0);
        assertEquals(2, node200_0.succSize());
        final Set<Transition> transitions200_0 = node200_0.getTransition();
        assertTrue(transitions200_0.contains(new Transition(t.fingerPrint(), 0, new BitSet(0))));
        assertTrue(transitions200_0.contains(new Transition(t.fingerPrint(), 1, new BitSet(0))));

        final GraphNode node200_1 = diskGraph.getNode(s.fingerPrint(), 1);
        assertEquals(2, node200_1.succSize());
        final Set<Transition> transitions200_1 = node200_1.getTransition();
        assertTrue(transitions200_1.contains(new Transition(t.fingerPrint(), 1, new BitSet(0))));
        assertTrue(transitions200_1.contains(new Transition(t.fingerPrint(), 2, new BitSet(0))));

        final GraphNode node200_2 = diskGraph.getNode(s.fingerPrint(), 2);
        assertEquals(0, node200_2.succSize());

        assertTrue(diskGraph.checkInvariants(0, 0));

        lc.close();
    }

    /**
     * @param s          The smallest state under symmetry
     * @param sSymmetric A symmetric state to s
     */
    private ILiveCheck getLiveCheckWithTwoNodeTableauSymmetry(final TLCState s, final TLCState sSymmetric, final TLCState t) throws Exception {
        final TBGraphNode node2 = EasyMock.createMock(TBGraphNode.class);
        // consistency
        final Capture<TLCState> capture = EasyMock.newCapture();
        EasyMock.expect(node2.isConsistent(EasyMock.capture(capture), EasyMock.anyObject())).andAnswer(() -> {
            final TLCState value = capture.getValue();
            return value != s;
        }).anyTimes();
        // index
        EasyMock.expect(node2.getIndex()).andReturn(2).anyTimes();
        // nextSize
        EasyMock.expect(node2.nextSize()).andReturn(1).anyTimes();
        // nextAt
        EasyMock.expect(node2.nextAt(0)).andReturn(node2).anyTimes();
        EasyMock.replay(node2);

        final TBGraphNode node1 = EasyMock.createMock(TBGraphNode.class);
        // consistency
        final Capture<TLCState> capture1 = EasyMock.newCapture();
        EasyMock.expect(node1.isConsistent(EasyMock.capture(capture1), EasyMock.anyObject())).andAnswer(() -> {
            final TLCState value = capture1.getValue();
            return value != sSymmetric;
        }).anyTimes();
        // index
        EasyMock.expect(node1.getIndex()).andReturn(1).anyTimes();
        // nextSize
        EasyMock.expect(node1.nextSize()).andReturn(2).anyTimes();
        // nextAt
        EasyMock.expect(node1.nextAt(0)).andReturn(node1).anyTimes();
        EasyMock.expect(node1.nextAt(1)).andReturn(node2).anyTimes();
        EasyMock.replay(node1);

        final TBGraphNode node0 = EasyMock.createMock(TBGraphNode.class);
        // consistency (simpler to node1 and node2)
        EasyMock.expect(node0.isConsistent(EasyMock.anyObject(), EasyMock.anyObject())).andReturn(true).anyTimes();
        // index
        EasyMock.expect(node0.getIndex()).andReturn(0).anyTimes();
        // nextSize
        EasyMock.expect(node0.nextSize()).andReturn(2).anyTimes();
        // nextAt
        EasyMock.expect(node0.nextAt(0)).andReturn(node0).anyTimes();
        EasyMock.expect(node0.nextAt(1)).andReturn(node1).anyTimes();
        EasyMock.replay(node0);

        final TBGraph tbGraph = new TBGraph();
        tbGraph.add(node0);
        tbGraph.add(node1);
        tbGraph.add(node2);
        tbGraph.setInitCnt(1);

        // Configure OOS mock to react to the subsequent invocation. This is a
        // essentially the list of calls being made on OOS during
        // LiveCheck#addInitState and LiveCheck#addNextState
        final OrderOfSolution oos = EasyMock.createNiceMock(OrderOfSolution.class);
        EasyMock.expect(oos.hasTableau()).andReturn(true);
        EasyMock.expect(oos.getTableau()).andReturn(tbGraph).anyTimes();
        EasyMock.expect(oos.getCheckAction()).andReturn(new LiveExprNode[0]).anyTimes();
        EasyMock.expect(oos.getCheckState()).andReturn(new LiveExprNode[0]).anyTimes();
        EasyMock.expect(oos.checkState(null, EasyMock.anyObject())).andReturn(new boolean[0]).anyTimes();
        EasyMock.replay(oos);

        final ITool tool = EasyMock.createNiceMock(ITool.class);
        EasyMock.expect(tool.hasSymmetry()).andReturn(true);
        final Capture<TLCState> nextStates = EasyMock.newCapture();
        EasyMock.expect(tool.getNextStates((Action) EasyMock.anyObject(), EasyMock.capture(nextStates))).andAnswer(() -> {
            final StateVec nss = new StateVec(0);
            // s > t for sSymmetric
            final TLCState state = nextStates.getValue();
            if (state == sSymmetric) {
                nss.addState(t);
            }
            return nss;
        });
        EasyMock.expect(tool.isInModel(EasyMock.anyObject())).andReturn(true).anyTimes();
        EasyMock.expect(tool.isInActions(EasyMock.anyObject(), EasyMock.anyObject())).andReturn(true).anyTimes();
        EasyMock.replay(tool);
        return new LiveCheck(tool,
                new OrderOfSolution[]{oos}, "states", new DummyBucketStatistics(), null);
    }
}
