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
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import org.junit.Test;

public class GraphNodeTest {

	@Test
	public void testAllocateRealign() {
		// Create a random graph node (fingerprint/tableau don't matter)
		final GraphNode node = new GraphNode(0, 0);

		int sizeHint = 5;
		node.addTransition(1, -1, -1, -1, null, 0, sizeHint--);
		node.addTransition(2, -1, -1, -1, null, 0, sizeHint--);
		node.addTransition(3, -1, -1, -1, null, 0, sizeHint--);
		node.addTransition(4, -1, -1, -1, null, 0, sizeHint--);
		node.addTransition(5, -1, -1, -1, null, 0, sizeHint--);

		int overallocated = node.realign();
		assertTrue("Allocation overallocated", overallocated == 0);

		assertTrue("Lost a transition during the allocation business", node.transExists(1, -1));
		assertTrue("Lost a transition during the allocation business", node.transExists(2, -1));
		assertTrue("Lost a transition during the allocation business", node.transExists(3, -1));
		assertTrue("Lost a transition during the allocation business", node.transExists(4, -1));
		assertTrue("Lost a transition during the allocation business", node.transExists(5, -1));
	}

	@Test
	public void testRealign() {
		// Create a random graph node (fingerprint/tableau don't matter)
		final GraphNode node = new GraphNode(0, 0);

		node.addTransition(1, -1, -1, -1, null, 0, 64);

		int overallocated = node.realign();
		assertTrue("Allocation overallocated", overallocated == 63);

		overallocated = node.realign();
		assertTrue("Allocation overallocated", overallocated == 0);

		assertTrue("Lost a transition during the allocation business", node.transExists(1, -1));
	}

	@Test
	public void testAllocateNested() {
		// Create a random graph node (fingerprint/tableau don't matter)
		final GraphNode node = new GraphNode(0, 0);

		int cnt = 0;
		for (int i = 0; i < 5; i++) {
			for (int j = 0; j < 10; j++) {
				for (int k = 0; k < 15; k++) {
					int l = (5 * 10 * 15);
					node.addTransition(cnt, -1, -1, -1, null, 0, l - cnt++);
				}
			}
		}
		int overallocated = node.realign();
		assertTrue("Nested allocation overallocated", overallocated == 0);

		for (int i = 0; i < cnt; i++) {
			assertTrue("Lost a transition during this allocation business", node.transExists(i, -1));
		}
	}

	@Test
	public void testAllocateNestedRandom() {
		// Create a random graph node (fingerprint/tableau don't matter)
		final GraphNode node = new GraphNode(0, 0);
		final Random rnd = new Random(4711);

		final List<Integer> verificationSet = new ArrayList<Integer>();
		
		int cnt = 0;
		for (int i = 0; i < 5; i++) {
			int x = rnd.nextInt(10);
			for (int j = 0; j < x; j++) {
				int y = rnd.nextInt(15);
				for (int k = 0; k < y; k++) {
					int l = (5 * x * y);
					int allocationHint = l - cnt++;
					node.addTransition(cnt, -1, -1, -1, null, 0, allocationHint);
					verificationSet.add(cnt);
				}
			}
		}

		for (Integer i : verificationSet) {
			assertTrue("Lost a transition during this allocation business", node.transExists(i, -1));
		}
	}

	@Test
	public void testAllocateNegative() {
		// Create a random graph node (fingerprint/tableau don't matter)
		final GraphNode node = new GraphNode(0, 0);
		node.addTransition(0, 0, 0, 0, null, 0, -1);
		assertTrue("overallocated", node.realign() == 0);
	}
	
	@Test
	public void testAllocateAndSuccessorSize() {
		// Hint to allocate 100 transitions and make sure the actual number of
		// transitions is 1.
		final GraphNode node = new GraphNode(0, 0);
		node.addTransition(0, 0, 0, 0, null, 0, 100);
		assertEquals(1, node.succSize());
	}
}
