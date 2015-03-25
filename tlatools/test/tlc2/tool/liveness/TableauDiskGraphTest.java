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

import java.io.IOException;

import junit.framework.TestCase;
import tlc2.util.BitVector;
import tlc2.util.LongVec;
import tlc2.util.statistics.BucketStatistics;

public class TableauDiskGraphTest extends TestCase {

	private static final String TMP_DIR = System.getProperty("java.io.tmpdir");
	private static final BucketStatistics GRAPH_STATS = new BucketStatistics("Test Dummy", 16);
	private static final int NUMBER_OF_SOLUTIONS = 1;
	private static final int NUMBER_OF_ACTIONS = 0;
	private static final BitVector NO_ACTIONS = null;
	
	// Tests that the path is correctly reconstructed when a node's predecessors
	// have an identical fingerprint but different tableau idxs.
	public void testGetShortestPath() throws IOException {
		final TableauDiskGraph dg = new TableauDiskGraph(TMP_DIR, NUMBER_OF_SOLUTIONS, GRAPH_STATS);

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
}
