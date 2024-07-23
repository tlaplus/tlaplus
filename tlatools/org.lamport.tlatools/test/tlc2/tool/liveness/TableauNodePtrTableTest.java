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

import java.util.Arrays;

import org.junit.Test;

public class TableauNodePtrTableTest {

	@Test
	public void testSetDoneBFSOrder() {
		
		// Test behavior of TNPT when state graph/fingerprint graph nodes are added in
		// strict BFS order.
		
		final TableauNodePtrTable tbl = new TableauNodePtrTable(0);
		
		final int DONE = 4711; // This is a disk location (pointer) in practice.
		final long fp = 42L; // hash(v) = fp
		final int t = 1;
		final int u = 2;		
		
		// 1) A transition from state u -> v is added into the behavior graph. As part
		// of adding u, TLC records v with some tableau ids.
		tbl.put(fp, t, TableauNodePtrTable.UNDONE);
		assertFalse(tbl.isDone(fp));
		tbl.put(fp, u, TableauNodePtrTable.UNDONE);
		assertFalse(tbl.isDone(fp));
		
		// 2) v -> ... is added into the behavior graph.
		tbl.setDone(fp);
		assertTrue(tbl.isDone(fp));
		
		// Marking the nodes done has become a no-op.
		tbl.put(fp, u, DONE);
		assertTrue(tbl.isDone(fp));
		tbl.put(fp, t, DONE);
		assertTrue(tbl.isDone(fp));
	}
	@Test
	public void testSetDoneNoOrder() {
		
		// Test behavior of TNPT when state graph/fingerprint graph nodes are added in
		// non-BFS order.
		
		final TableauNodePtrTable tbl = new TableauNodePtrTable(0);
		
		final int DONE = 4711; // This is a disk location (pointer) in practice.
		final long fp = 42L; // hash(v) = fp
		final int t = 1;
		final int u = 2;		
		
		// 1) A transition from state v -> ... is added into the behavior graph. Because
		// v has not been recorded earlier, adding it into the behavior graph is reduced
		// to calling setDone; no GraphNodes are recorded.
		tbl.setDone(fp);
		assertTrue(tbl.isDone(fp));

		// 2) u -> v is added into the behavior graph.
		tbl.put(fp, t, TableauNodePtrTable.UNDONE);
		assertFalse(tbl.isDone(fp));
		tbl.put(fp, u, TableauNodePtrTable.UNDONE);
		assertFalse(tbl.isDone(fp));
				
		// Marking the nodes done has become a no-op.
		tbl.put(fp, u, DONE);
		assertFalse(tbl.isDone(fp));
		tbl.put(fp, t, DONE);
		assertTrue(tbl.isDone(fp));
	}

	@Test
	public void testSetDone() {
		final TableauNodePtrTable tbl = new TableauNodePtrTable(0); // init with 0 so that grow is tested
		
		final long fingerprint = 1L;
		assertFalse(tbl.isDone(fingerprint));
		
		tbl.setDone(fingerprint);
		assertTrue(tbl.isDone(fingerprint));
		
		tbl.put(fingerprint, 1, TableauNodePtrTable.UNDONE);
		// This ends up as -2 for the high part of the long and thus tbl isn't
		// done anymore.
		assertFalse(tbl.isDone(fingerprint));

		// Add another node BUT with different tableau index. The done state
		// does NOT change.
		tbl.put(fingerprint, 2, 4711L);
		assertFalse(tbl.isDone(fingerprint));

		tbl.setDone(fingerprint);
		assertTrue(tbl.isDone(fingerprint));
	}

	@Test
	public void testSetDone2() {
		final TableauNodePtrTable tbl = new TableauNodePtrTable(0);
		
		final int DONE = 4711; // This is a disk location (pointer) in practice.
		final long fp = 42L;
		final int t = 1;
		final int u = 2;		
		
		// Mark fp as done.
		tbl.setDone(fp);
		assertTrue(tbl.isDone(fp));
		
		// Add the behavior graph node <<fp, t>> to tbl and mark it undone.
		tbl.put(fp, t, TableauNodePtrTable.UNDONE);
		
		// Adding <<fp, t>> to tbl causes fp to become undone again!!!
		assertFalse(tbl.isDone(fp));

		// Add a second node <<fp, u>> to the behavior graph (same fingerprint but different
		// tableau node).
		tbl.put(fp, u, TableauNodePtrTable.UNDONE);
		
		// Nothing changes WRT fp.
		assertFalse(tbl.isDone(fp));
		
		// Marking the additional node done has no effect on fp's done state.
		tbl.put(fp, u, DONE);
		assertFalse(tbl.isDone(fp));
		
		// Marking the *first* node (insertion order) in tbl done, marks fp done again. 
		tbl.put(fp, t, DONE);
		assertTrue(tbl.isDone(fp));
	}

	@Test
	public void testSetDone3() {
		final TableauNodePtrTable tbl = new TableauNodePtrTable(0);
		
		final int DONE = 4711; // This is a disk location (pointer) in practice.
		final long fp = 42L;
		final int t = 1;
		final int u = 2;		
		
		tbl.setDone(fp);
		assertTrue(tbl.isDone(fp));
		
		// fp becomes undone again by recording a node (see dgragh.recordNode)
		tbl.put(fp, t, TableauNodePtrTable.UNDONE);
		assertFalse(tbl.isDone(fp));

		// nothing changes if we record additional nodes.
		tbl.put(fp, u, TableauNodePtrTable.UNDONE);
		assertFalse(tbl.isDone(fp));
		
		// Mark the initial node done.
		tbl.put(fp, t, DONE);
		assertTrue(tbl.isDone(fp));
	}
	
	// Test various methods which apparently all yield pretty much the same result
	@Test
	public void testRedundantMethodYieldSameResult() {
		final TableauNodePtrTable tbl = new TableauNodePtrTable(0); // init with 0 so that grow is tested
		
		final long fingerprint = 1L;
		
		assertEquals(-1, tbl.getNodesLoc(fingerprint));
		
		final int loc = tbl.setDone(fingerprint);
		assertTrue(tbl.isDone(fingerprint));

		assertTrue(tbl.getNodesLoc(fingerprint) != -1);
		assertEquals(tbl.getNodesLoc(fingerprint), loc);

		assertTrue(Arrays.equals(tbl.getNodesByLoc(loc), tbl.getNodes(fingerprint)));

		assertEquals(-1, tbl.getLoc(fingerprint, 1));
		tbl.addElem(fingerprint, 1, 2342);
		// Cannot lookup after addElem
		assertEquals(-1, tbl.getLoc(fingerprint, 1));
		
		//...have to put instead
		tbl.put(fingerprint, 1, 2342);
		assertTrue(tbl.getLoc(fingerprint, 1) != -1);
	}
}
