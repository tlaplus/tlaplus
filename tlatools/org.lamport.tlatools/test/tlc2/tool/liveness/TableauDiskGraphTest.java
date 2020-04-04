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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.IOException;

import org.junit.Test;

import tlc2.util.BitVector;
import tlc2.util.LongVec;
import tlc2.util.statistics.FixedSizedBucketStatistics;
import tlc2.util.statistics.IBucketStatistics;

public class TableauDiskGraphTest extends DiskGraphTest {

	private static final IBucketStatistics GRAPH_STATS = new FixedSizedBucketStatistics("Test Dummy", 16);
	private static final int NUMBER_OF_SOLUTIONS = 1;
	private static final int NUMBER_OF_ACTIONS = 0;
	private static final BitVector NO_ACTIONS = null;
	
	
	
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.DiskGraphTest#getDiskGraph()
	 */
	protected AbstractDiskGraph getDiskGraph() throws IOException {
		return new TableauDiskGraph(createTempDirectory().getAbsolutePath(), NUMBER_OF_SOLUTIONS, GRAPH_STATS);
	}

	/* 
	 * Tests that the path is correctly reconstructed when a node's predecessors
	 * have an identical fingerprint but different tableau indices.
	 * 
	 *                  +------+                          
	 *	+-------+       |      |                          
	 *	|       |       |second+---------+                
	 *	| init  +-----> |0     |         |                
	 *	|       |       +------+         ^                
	 *	+-------+       +------+     +---+--+     +------+
	 *	                |(init)|     |      |     |      |
	 *	                |second+----->third +----->final |
	 *	+-------+       |1     |     |      |     |      |
	 *	|       |       +------+     +---+--+     +------+
	 *	| init  |       +------+         ^                
	 *	|       +-----> |      |         |                
	 *	+-------+       |second+---------+                
	 *	                |2     |                          
	 *	                +------+                           
	 *
	 */
	@Test
	public void testGetShortestPath() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();

		long initState = 1L;
		int initTableauIdx = 0;
		
		long secondState = 2L;
		// Its tableau indices range from 0 to 2. Tableau idx
		// 1 is an init state too.

		long thirdState = 3L;
		int thirdTableauIdx = 0;
				
		long finalState = 4L;
		int finalTableauIdx = 0;
		
		// init#1
		dg.addInitNode(initState, initTableauIdx);
		// second#1
		dg.addInitNode(secondState, 1);
		
		// Init#1
		GraphNode node = new GraphNode(initState, initTableauIdx);
		node.addTransition(secondState, 0, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		node.addTransition(secondState, 2, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		dg.addNode(node);
		
		// second#0
		node = new GraphNode(secondState, 0);
		node.addTransition(thirdState, thirdTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		dg.addNode(node);
		// second#1
		node = new GraphNode(secondState, 1);
		node.addTransition(thirdState, thirdTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		dg.addNode(node);
		// second#2
		node = new GraphNode(secondState, 2);
		node.addTransition(thirdState, thirdTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		dg.addNode(node);
		
		// third#0
		node = new GraphNode(thirdState, thirdTableauIdx);
		node.addTransition(finalState, finalTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		dg.addNode(node);
		
		// final#0
		node = new GraphNode(finalState, finalTableauIdx);
		dg.addNode(node);
		
		dg.createCache();
		final LongVec path = dg.getPath(finalState, finalTableauIdx);
		dg.destroyCache();
		
		// It is important that it finds the shortest path.
		assertEquals(3, path.size());
		assertEquals(finalState, path.elementAt(0));
		assertEquals(thirdState, path.elementAt(1));
		assertEquals(secondState, path.elementAt(2));
	}

	/*
	 *                       +---------+                        
	 *	                     |         |                        
	 *	     +--------------->  second +------------------+     
	 *	     |               |         |                  |     
	 *	     |               +---------+                  |     
	 *	     |                                            |     
	 *	+----+---+                                   +----v----+
	 *	|        |                                   |         |
	 *	| init   |                                   | final   |
	 *	|        |                                   |         |
	 *	+----+---+                                   +----+----+
	 *	     |                                            ^     
	 *	     |                +---------+                 |     
	 *	     |                |         |                 |     
	 *	     +---------------->  third  +-----------------+     
	 *	                      |         |                       
	 *	                      +---------+                        
 	 *
	 * (Drawn with http://asciiflow.com/)
	 */
	@Test
	public void testUnifyingNodeInPath() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();

		long initState = 1L;
		int initTableauIdx = 0;
		
		long secondState = 2L;
		int secondTableauIdx = 0;

		long thirdState = 3L;
		int thirdTableauIdx = 0;
				
		long finalState = 4L;
		int finalTableauIdx = 0;
		
		// Init
		dg.addInitNode(initState, initTableauIdx);
		
		// Init
		GraphNode node = new GraphNode(initState, initTableauIdx);
		
		/*
		 * The *order* in which the transitions are added to the init node define,
		 * which one of the two possible pathes is later found. Since we add
		 * the second state first, the path will be final -> second -> init
		 */
		node.addTransition(secondState, secondTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		node.addTransition(thirdState, thirdTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		
		dg.addNode(node);
		
		// second
		node = new GraphNode(secondState, secondTableauIdx);
		node.addTransition(finalState, finalTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		dg.addNode(node);
		
		// third
		node = new GraphNode(thirdState, thirdTableauIdx);
		node.addTransition(finalState, finalTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		dg.addNode(node);
		
		// final
		node = new GraphNode(finalState, finalTableauIdx);
		dg.addNode(node);
		
		dg.createCache();
		final LongVec path = dg.getPath(finalState, finalTableauIdx);
		dg.destroyCache();
		
		// There are now two path with identical length:
		// init -> second -> final & init -> third -> final
		// and both are correct path.
		assertEquals(3, path.size());
		assertEquals(finalState, path.elementAt(0));
		assertEquals(secondState, path.elementAt(1));
		assertEquals(initState, path.elementAt(2));
	}

	/*
	 * Similar to testUnifiyingNodeInPath except that the upper path has one
	 * extra node. This should mean that the search returns init -> third ->
	 * final because it is shorter regardless of second being added as a
	 * transition first.
	 *
	 *              +---------+       +---------+                        
	 *	            |         |       |         |                        
	 *	     +------>  frob   +------->  second +---------+     
	 *	     |      |         |       |         |         |     
	 *	     |      +---------+       +---------+         |     
	 *	     |                                            |     
	 *	+----+---+                                   +----v----+
	 *	|        |                                   |         |
	 *	| init   |                                   | final   |
	 *	|        |                                   |         |
	 *	+----+---+                                   +----+----+
	 *	     |                                            ^     
	 *	     |                +---------+                 |     
	 *	     |                |         |                 |     
	 *	     +---------------->  third  +-----------------+     
	 *	                      |         |                       
	 *	                      +---------+                        
	 */
	@Test
	public void testUnifyingNodeShortestPath() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();

		long initState = 1L;
		int initTableauIdx = 0;
		
		long frob = 5;
		int frobTableauIdx = 0;
		
		long secondState = 2L;
		int secondTableauIdx = 0;

		long thirdState = 3L;
		int thirdTableauIdx = 0;
				
		long finalState = 4L;
		int finalTableauIdx = 0;
		
		// Init
		dg.addInitNode(initState, initTableauIdx);
		
		// Init
		GraphNode node = new GraphNode(initState, initTableauIdx);
		
		/*
		 * The *order* in which the transitions are added to the init node define,
		 * which one of the two possible pathes is later found. Since we add
		 * the second state first, the path will be final -> second -> init
		 */
		node.addTransition(frob, frobTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		node.addTransition(thirdState, thirdTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		
		dg.addNode(node);
		
		// frob
		node = new GraphNode(frob, frobTableauIdx);
		node.addTransition(secondState, secondTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		dg.addNode(node);
		
		
		// second
		node = new GraphNode(secondState, secondTableauIdx);
		node.addTransition(finalState, finalTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		dg.addNode(node);
		
		// third
		node = new GraphNode(thirdState, thirdTableauIdx);
		node.addTransition(finalState, finalTableauIdx, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 1);
		dg.addNode(node);
		
		// final
		node = new GraphNode(finalState, finalTableauIdx);
		dg.addNode(node);
		
		dg.createCache();
		final LongVec path = dg.getPath(finalState, finalTableauIdx);
		dg.destroyCache();
		
		// There are now two path with identical length:
		// init -> second -> final & init -> third -> final
		// and both are correct path.
		assertEquals(3, path.size());
		assertEquals(finalState, path.elementAt(0));
		assertEquals(thirdState, path.elementAt(1));
		assertEquals(initState, path.elementAt(2));
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
	 * The specialty here is that there are *two* init nodes and one them has *no* successors.
	 * 
	 * @see Bug #293 in general/bugzilla/index.html
	 */
	@Test
	public void testPathWithTwoInitNodesWithTableau() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();

		long noSuccessorInitState = 1L;

		long regularInitState = 2L;
		
		long finalState = 3L;

		// Init
		dg.addInitNode(noSuccessorInitState, 0);
		
		/*
		 * Intentionally *NOT* adding the init via dg.addNode(init)
		 */
		
		// second init (this one gets added via addNode
		dg.addInitNode(regularInitState, 0);
		GraphNode node = new GraphNode(regularInitState, 0);
		node.addTransition(finalState, 0, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);
		
		// final
		node = new GraphNode(finalState, 0);
		dg.addNode(node);
		
		dg.createCache();
		LongVec path = dg.getPath(finalState, 0);
		dg.destroyCache();
		
		assertEquals(2, path.size());
		assertEquals(finalState, path.elementAt(0));
		assertEquals(regularInitState, path.elementAt(1));
		
		// Make sure it also returns a path if init is searched
		dg.createCache();
		path = dg.getPath(noSuccessorInitState, 0);
		dg.destroyCache();

		assertEquals(1, path.size());
		assertEquals(noSuccessorInitState, path.elementAt(0));
	}
	
	/*
	 * Test that getPath returns the correct init state if the graph contains
	 * multiple initial states with the same fingerprint but different tableau idxs.
	 */
	@Test
	public void testGetPathWithTwoInits() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();
		
		final long fingerprint = 1L;
		
		dg.addInitNode(fingerprint, 0);
		dg.addInitNode(fingerprint, 1);
		
		try {
			// Requesting path to node with tidx 2 is supposed to fail when no
			// such node is in the graph.
			dg.createCache();
			dg.getPath(fingerprint, 2);
			dg.destroyCache();
		} catch (RuntimeException e) {
			// Now that it has been added, it should be found.
			dg.addInitNode(fingerprint, 2);
			
			dg.createCache();
			LongVec path = dg.getPath(fingerprint, 2);
			dg.destroyCache();
			
			assertEquals(1, path.size());
			assertEquals(fingerprint, path.elementAt(0));
			return;
		}
		fail("Returned path to non-existing node");
	}
	
	/*
	 * Test how an initial node transitions through the done state
	 */
	@Test
	public void testNodeSetDone() throws IOException {
		final TableauDiskGraph dg = (TableauDiskGraph) getDiskGraph();
		final long fingerprint = 1L;

		// Adding as init leaves the node in the undone state
		dg.addInitNode(fingerprint, 0);
		assertFalse(dg.isDone(fingerprint));

		// Adding it with addNextState changes the done state to being done.
		GraphNode node = new GraphNode(fingerprint, 0);
		node.addTransition(fingerprint, 1, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);

		// It is done now
		assertTrue(dg.isDone(fingerprint));
	}
	
	/*
	 * Tests a path where both states have an identical fingerprint and only
	 * differ in the tableau idx.
	 */
	@Test
	public void testGetPathWithTwoNodesWithSameFingerprint() throws IOException {
		final AbstractDiskGraph dg = getDiskGraph();

		final long fingerprint = 1L;

		// first
		dg.addInitNode(fingerprint, 0);
		GraphNode node = new GraphNode(fingerprint, 0);
		node.addTransition(fingerprint, 1, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);
		
		// second
		node = new GraphNode(fingerprint, 1);
		dg.addNode(node);

		
		dg.createCache();
		final LongVec path = dg.getPath(fingerprint, 1);
		dg.destroyCache();

		assertEquals(2, path.size());
		assertEquals(fingerprint, path.elementAt(0));
		assertEquals(fingerprint, path.elementAt(1));
	}
	
	/*
	 * Test that it is possible to "update" a GraphNode's outgoing transitions.
	 */
	@Test
	public void testLookupExistingNodeWithTidx() throws IOException {
		final TableauDiskGraph dg = (TableauDiskGraph) getDiskGraph();
		
		GraphNode node = dg.getNode(1L, 1);
		assertEquals(0, node.succSize());
		dg.addNode(node);
		
		// Cause the DiskGraph to be read from disk
		dg.makeNodePtrTbl();
		
		node = dg.getNode(1L, 1);
		dg.addNode(node);
		assertEquals(0, node.succSize());
		
		node.addTransition(2, 2, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);
		assertEquals(1, node.succSize());
		assertTrue(node.transExists(2, 2));
		
		dg.makeNodePtrTbl();
		
		node = dg.getNode(1L, 1);
		assertEquals(1, node.succSize());

		node.addTransition(3, 3, NUMBER_OF_SOLUTIONS, NUMBER_OF_ACTIONS, NO_ACTIONS,
				NUMBER_OF_ACTIONS, 0);
		dg.addNode(node);
		assertEquals(2, node.succSize());
		assertTrue(node.transExists(2, 2));
		assertTrue(node.transExists(3, 3));
		
		// commit/chkpt
		dg.beginChkpt();
		dg.commitChkpt();
		dg.recover();
		
		node = dg.getNode(1L, 1);
		assertEquals(2, node.succSize());
		assertTrue(node.transExists(2, 2));
		assertTrue(node.transExists(3, 3));
	}
}
