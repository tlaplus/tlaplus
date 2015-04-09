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

import java.util.Arrays;

import junit.framework.TestCase;

public class TableauNodePtrTableTest extends TestCase {

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
	
	// Test various methods which apparently all yield pretty much the same result
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
