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

package tlc2.tool.liveness.simulation;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

import java.io.IOException;

import org.easymock.EasyMock;
import org.junit.Before;
import org.junit.Test;

import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.liveness.AbstractDiskGraph;
import tlc2.tool.liveness.ILiveCheck;
import tlc2.tool.liveness.LiveCheck;
import tlc2.tool.liveness.LiveExprNode;
import tlc2.tool.liveness.OrderOfSolution;
import tlc2.tool.liveness.TBGraph;
import tlc2.tool.liveness.TBGraphNode;
import tlc2.tool.queue.DummyTLCState;
import tlc2.util.SetOfStates;
import tlc2.util.statistics.DummyBucketStatistics;

public class LiveCheckTest {

	private ITool tool;
	
	@Before
	public void createTool() {
		this.tool = EasyMock.createNiceMock(ITool.class);
	}

	// Add identical state twice, which can happen in simulation mode when the
	// trace is: <<100L, 200L, ..., 100L, 200L>> (as in a cycle that is
	// repeated due to the trace length). In this scenario DiskGraph should
	// *not* add/update the 100L state, because it's successors (200L) don't
	// change.
	// Note that adding/updating the state would result in a larger
	// on-disk file, but doesn't seem to invalidate the simulation validity.
	@Test
	public void testAddIdenticalNodeTwiceNoTableau() throws IOException {
		addIdenticalNodeTwice(false, -1);
	}

	@Test
	public void testAddIdenticalNodeTwiceWithTableau() throws IOException {
		addIdenticalNodeTwice(true, 0);
	}

	public void addIdenticalNodeTwice(boolean withTablue, int tableauId) throws IOException {
		final ILiveCheck liveCheck;
		if (withTablue) {
			liveCheck = getLiveCheckWithTableau();
		} else {
			liveCheck = getLiveCheck();
		}

		assertEquals(1, liveCheck.getNumChecker());
		final AbstractDiskGraph diskGraph = liveCheck.getChecker(0).getDiskGraph();
		assertNotNull(diskGraph);
		
		final TLCState state = new DummyTLCState();
		liveCheck.addInitState(tool, state, 100L);

		final SetOfStates setOfStates = new SetOfStates(1);
		setOfStates.put(200L, new DummyTLCState(200L));
		
		// Add state 100L the first time, then add its successor
		liveCheck.addNextState(tool, state, 100L, setOfStates);
		liveCheck.addNextState(tool, state, 200L, setOfStates);
		assertEquals(0, diskGraph.getPtr(100L, tableauId));

		// Add state 100L again and check that it does *not* 
		// end up in disk graph.
		liveCheck.addNextState(tool, state, 100L, setOfStates);
		assertEquals(0, diskGraph.getPtr(100L, tableauId));
	}

	private ILiveCheck getLiveCheck() throws IOException {
		final ITool tool = EasyMock.createNiceMock(ITool.class);
		// Configure OOS mock to react to the subsequent invocation. This is
		// essentially the list of calls being made on OOS during
		// LiveCheck#addInitState and LiveCheck#addNextState
		final OrderOfSolution oos = EasyMock.createNiceMock(OrderOfSolution.class);
		EasyMock.expect(oos.hasTableau()).andReturn(false);
		EasyMock.expect(oos.getCheckAction()).andReturn(new LiveExprNode[0]).anyTimes();
		EasyMock.expect(oos.checkState((ITool) EasyMock.anyObject(), (TLCState) EasyMock.anyObject())).andReturn(new boolean[0]).anyTimes();
		EasyMock.replay(oos);
		
		return new LiveCheck(tool,
				new OrderOfSolution[] { oos }, System.getProperty("java.io.tmpdir"), new DummyBucketStatistics());
	}
	
	private ILiveCheck getLiveCheckWithTableau() throws IOException {
		final TBGraphNode node = EasyMock.createMock(TBGraphNode.class);
		EasyMock.expect(node.isConsistent((TLCState) EasyMock.anyObject(), (ITool) EasyMock.anyObject())).andReturn(true)
				.anyTimes();
		EasyMock.expect(node.nextSize()).andReturn(1).anyTimes();
		EasyMock.expect(node.nextAt(0)).andReturn(node).anyTimes();
		EasyMock.expect(node.getIndex()).andReturn(0).anyTimes();
		EasyMock.replay(node);
		
		final TBGraph tbGraph = new TBGraph();
		tbGraph.addElement(node);
		tbGraph.setInitCnt(1);
		
		// Configure OOS mock to react to the subsequent invocation. This is a
		// essentially the list of calls being made on OOS during
		// LiveCheck#addInitState and LiveCheck#addNextState
		final OrderOfSolution oos = EasyMock.createNiceMock(OrderOfSolution.class);
		EasyMock.expect(oos.hasTableau()).andReturn(true);
		EasyMock.expect(oos.getTableau()).andReturn(tbGraph).anyTimes();
		EasyMock.expect(oos.getCheckAction()).andReturn(new LiveExprNode[0]).anyTimes();
		EasyMock.expect(oos.checkState((ITool) EasyMock.anyObject(), (TLCState) EasyMock.anyObject())).andReturn(new boolean[0]).anyTimes();
		EasyMock.replay(oos);
		
		return new LiveCheck(tool,
				new OrderOfSolution[] { oos }, System.getProperty("java.io.tmpdir"), new DummyBucketStatistics());
	}
}

