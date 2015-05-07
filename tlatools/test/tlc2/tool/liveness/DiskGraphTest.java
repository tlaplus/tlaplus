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

import java.io.File;
import java.io.IOException;

import junit.framework.TestCase;
import tlc2.util.BitVector;
import tlc2.util.LongVec;
import tlc2.util.statistics.BucketStatistics;
import tlc2.util.statistics.IBucketStatistics;

public class DiskGraphTest extends TestCase {

	private static final IBucketStatistics GRAPH_STATS = new BucketStatistics("Test Dummy", 16);
	private static final int NUMBER_OF_SOLUTIONS = 1;
	private static final int NO_TABLEAU = -1;
	private static final int NUMBER_OF_ACTIONS = 0;
	private static final BitVector NO_ACTIONS = null;
	
	protected AbstractDiskGraph getDiskGraph() throws IOException {
		// Have to use dedicated folder for each test. Otherwise tests interfere
		// with each other (e.g. test A reads the disk file of test B)
		return new DiskGraph(createTempDirectory().getAbsolutePath(), NUMBER_OF_SOLUTIONS, GRAPH_STATS);
	}

	protected File createTempDirectory() throws IOException {
		final File temp;
		temp = File.createTempFile("temp", Long.toString(System.nanoTime()));
		if (!(temp.delete())) {
			throw new IOException("Could not delete temp file: " + temp.getAbsolutePath());
		}
		if (!(temp.mkdir())) {
			throw new IOException("Could not create temp directory: " + temp.getAbsolutePath());
		}
		return temp;
	}
	
	// No init node makes DiskGraph#getPath never break from the while loop
	public void testGetPathWithoutInitNoTableau() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		dg.addNode(new GraphNode(1L, NO_TABLEAU));
		dg.createCache();
		try {
			dg.getPath(1L, -1);
		} catch (RuntimeException e) {
			return;
		}
		fail("getPath() without init nodes has to throw a RuntimeException");
	}

	// Create a linear minimal graph (2 nodes) and check if the graph is
	// returned by getPath afterwards.
	public void testGetMinimalPathWithoutTableau() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();

		final long initFP = 1L;
		final long successorFP = 2L;
		
		// Init node
		dg.addInitNode(1L, NO_TABLEAU);

		// Successor node
		dg.addNode(new GraphNode(successorFP, NO_TABLEAU));
		
		// Create relationship between init and successor
		final GraphNode node = new GraphNode(initFP, NO_TABLEAU);
		node.addTransition(successorFP, NO_TABLEAU, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS, NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);

		// Can only lookup/get a node, if there is a cache
		dg.createCache();
		final LongVec path = dg.getPath(successorFP, -1);
		dg.destroyCache();

		assertFalse("Length or path returned is too short", path.size() < 2);
		assertFalse("Length or path returned is too long", path.size() > 2);
	}
	
	/*
	 * +----------+                   
	 * |          |                   
	 * | init     |                   
	 * |          |                   
	 * |          |                   
	 * +----------+                   
	 *                                
	 * +----------+       +----------+
	 * |          |       |          |
	 * | second   +------->  final   |
	 * | init     |       |          |
	 * |          |       |          |
	 * +----------+       +----------+
	 * 
	 * The specialty here is that there are *two* init nodes and one of them has *no* successors.
	 * 
	 * @see https://bugzilla.tlaplus.net/show_bug.cgi?id=293
	 */
	public void testPathWithTwoInitNodes() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();

		long noSuccessorInitState = 1L;

		long regularInitState = 2L;
		
		long finalState = 3L;

		// Init
		dg.addInitNode(noSuccessorInitState, NO_TABLEAU);
		
		/*
		 * Intentionally *NOT* adding the init via dg.addNode(init)
		 */
		
		// second init (this one gets added via addNode
		dg.addInitNode(regularInitState, NO_TABLEAU);
		GraphNode node = new GraphNode(regularInitState, NO_TABLEAU);
		node.addTransition(finalState, NO_TABLEAU, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);
		
		// final
		node = new GraphNode(finalState, NO_TABLEAU);
		dg.addNode(node);
		
		dg.createCache();
		LongVec path = dg.getPath(finalState, NO_TABLEAU);
		dg.destroyCache();
		
		assertEquals(2, path.size());
		assertEquals(finalState, path.elementAt(0));
		assertEquals(regularInitState, path.elementAt(1));

		// Make sure it also returns a path if init is searched
		dg.createCache();
		path = dg.getPath(noSuccessorInitState, NO_TABLEAU);
		dg.destroyCache();

		assertEquals(1, path.size());
		assertEquals(noSuccessorInitState, path.elementAt(0));
	}
	
	/*
	 * Make sure the same logical node isn't counted twice.
	 */
	public void testAddSameGraphNodeTwice() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		dg.addNode(new GraphNode(1L, 1));
		dg.addNode(new GraphNode(1L, 1));
		assertEquals(1, dg.size());
	}
	
	
	/*
	 * Test that it is possible to "update" a GraphNode's outgoing transitions.
	 */
	public void testLookupExistingNode() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		
		GraphNode node = dg.getNode(1L, -1);
		assertEquals(0, node.succSize());
		dg.addNode(node);
		
		// Cause the DiskGraph to be read from disk
		dg.makeNodePtrTbl();
		
		node = dg.getNode(1L, -1);
		dg.addNode(node);
		assertEquals(0, node.succSize());
		
		node.addTransition(2, -1, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);
		assertEquals(1, node.succSize());
		assertTrue(node.transExists(2, -1));
		
		dg.makeNodePtrTbl();
		
		node = dg.getNode(1L, -1);
		assertEquals(1, node.succSize());

		node.addTransition(3, -1, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);
		assertEquals(2, node.succSize());
		assertTrue(node.transExists(2, -1));
		assertTrue(node.transExists(3, -1));
		
		// commit/chkpt
		dg.beginChkpt();
		dg.commitChkpt();
		dg.recover();
		
		node = dg.getNode(1L, -1);
		assertEquals(2, node.succSize());
		assertTrue(node.transExists(2, -1));
		assertTrue(node.transExists(3, -1));
	}
	
	/*
	 * Test that adding a GraphNode twice (same fingerprint & tableau idx) but
	 * with different successors afterwards yields the union of the successors.
	 */
	public void testAddSameGraphNodeTwiceCorrectSuccessors() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();

		// Add a graphnode to DiskGraph with a single transition
		final GraphNode graphNode = dg.getNode(1, NO_TABLEAU);
		graphNode.addTransition(2, NO_TABLEAU, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		long firstPtr = dg.addNode(graphNode);
		
		// Update the same graph node with another transition
		final GraphNode graphNodeSecondInstance = dg.getNode(1, NO_TABLEAU);
		graphNodeSecondInstance.addTransition(3, NO_TABLEAU, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		long secondPtr = dg.addNode(graphNodeSecondInstance);
		
		assertEquals(1, dg.size());
		
		assertNotSame(firstPtr, secondPtr);
		assertEquals(secondPtr, dg.getLink(1, NO_TABLEAU));

		final GraphNode node = dg.getNode(1, NO_TABLEAU);
		assertEquals(2, node.succSize());
		assertTrue(node.transExists(2, NO_TABLEAU));
		assertTrue(node.transExists(3, NO_TABLEAU));
		
		dg.makeNodePtrTbl();
		dg.createCache();
		final long ptr = dg.getLink(1, NO_TABLEAU);
		final GraphNode n = dg.getNode(1, NO_TABLEAU, ptr);
		assertEquals(2, n.succSize());
		assertTrue(n.transExists(2, NO_TABLEAU));
		assertTrue(n.transExists(3, NO_TABLEAU));
	}
	
	/*
	 * Test to verify that getPath does not throw an ArrayIndexOutOfBounds due
	 * to nextLoc being -1. This used to happen intermittently when liveness
	 * checking runs periodically on an incomplete state/behavior graph, a
	 * liveness violation is found and the path of the error trace gets explored.
	 */
	public void testGetPathPartialGraph() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		
		final long initState = 2L;
		final long danglingState = 3L;

		// Init
		dg.addInitNode(initState, NO_TABLEAU);
		final GraphNode node = new GraphNode(initState, NO_TABLEAU);
		node.addTransition(danglingState, NO_TABLEAU, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);

		/*
		 * The dangling state does not get added on purpose to simulate a
		 * partial graph.
		 */
	
		// Now get the path to some non-existing state (to explore all states in
		// the graph)
		dg.createCache();
		try {
			dg.getPath(5L, NO_TABLEAU);
		} catch (ArrayIndexOutOfBoundsException e) {
			fail(e.getMessage());
		} catch (RuntimeException e) {
			// Make sure it is the correct RuntimeException
			assertEquals("Couldn't re-create liveness trace (path) starting at: 5 and tidx: -1", e.getMessage());
		}
	}
}
