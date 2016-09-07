/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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
package tlc2.tool.fp;

import java.rmi.RemoteException;

import org.junit.Assert;
import org.junit.Test;

import tlc2.tool.fp.OffHeapDiskFPSet.Indexer;

public class OffHeapIndexerTest {

	@Test
	public void testBitshifting() throws RemoteException {
		final int fpBits = 1;
		final long positions = 128L;
		final int logPos = 8;
		doTest(fpBits, positions, logPos, new OffHeapDiskFPSet.BitshiftingIndexer(positions, fpBits));
	}

	@Test
	public void testRescale() throws RemoteException {
		final int fpBits = 1;
		final long positions = 96L;
		
		final Indexer indexer = new OffHeapDiskFPSet.Indexer(positions, fpBits);

		// indexer spreads over all positions
		Assert.assertEquals(0, indexer.getIdx(1, 0));
		Assert.assertEquals(48, indexer.getIdx(((0xFFFFFFFFFFFFFFFFL >>> fpBits) / 2L)));
		Assert.assertEquals(positions - 1, indexer.getIdx((0xFFFFFFFFFFFFFFFFL >>> fpBits)));
		
		// Correctly wraps around when end of array is reached
		Assert.assertEquals(0, indexer.getIdx((0xFFFFFFFFFFFFFFFFL >>> fpBits), 1));
		// Correctly wraps around when end of array is reached twice
		Assert.assertEquals(0, indexer.getIdx((0xFFFFFFFFFFFFFFFFL >>> fpBits), (int)positions+1));
	}

	@Test
	public void testRescale99() throws RemoteException {
		final int fpBits = 1;
		final long positions = 99L;
		
		final Indexer indexer = new OffHeapDiskFPSet.Indexer(positions, fpBits);

		// indexer spreads over all positions
		Assert.assertEquals(0, indexer.getIdx(1));
		Assert.assertEquals(49, indexer.getIdx(((0xFFFFFFFFFFFFFFFFL >>> fpBits) / 2L)));
		Assert.assertEquals(positions - 1, indexer.getIdx((0xFFFFFFFFFFFFFFFFL >>> fpBits)));
		
		// Correctly wraps around when end of array is reached
		Assert.assertEquals(0, indexer.getIdx((0xFFFFFFFFFFFFFFFFL >>> fpBits), 1));
		// Correctly wraps around when end of array is reached twice
		Assert.assertEquals(0, indexer.getIdx((0xFFFFFFFFFFFFFFFFL >>> fpBits), (int)positions+1));
	}

	@Test
	public void testBitshifting2() throws RemoteException {
		final int fpBits = 2;
		final long positions = 128L;
		final int logPos = 9;
		doTest(fpBits, positions, logPos, new OffHeapDiskFPSet.BitshiftingIndexer(positions, fpBits));
	}

	@Test
	public void testRescale2() throws RemoteException {
		final int fpBits = 2;
		final long positions = 96L;
		
		final Indexer indexer = new OffHeapDiskFPSet.Indexer(positions, fpBits);

		// indexer spreads over all positions
		Assert.assertEquals(0, indexer.getIdx(1));
		Assert.assertEquals(48, indexer.getIdx(((0xFFFFFFFFFFFFFFFFL >>> fpBits) / 2L)));
		Assert.assertEquals(95, indexer.getIdx((0xFFFFFFFFFFFFFFFFL >>> fpBits)));
		
		// Correctly wraps around when end of array is reached
		Assert.assertEquals(0, indexer.getIdx((0xFFFFFFFFFFFFFFFFL >>> fpBits), 1));
		// Correctly wraps around when end of array is reached twice
		Assert.assertEquals(0, indexer.getIdx((0xFFFFFFFFFFFFFFFFL >>> fpBits), 97));
	}

	@Test
	public void testRescale299() throws RemoteException {
		final int fpBits = 2;
		final long positions = 99L;
		
		final Indexer indexer = new OffHeapDiskFPSet.Indexer(positions, fpBits);

		// indexer spreads over all positions
		Assert.assertEquals(0, indexer.getIdx(1));
		Assert.assertEquals(49, indexer.getIdx(((0xFFFFFFFFFFFFFFFFL >>> fpBits) / 2L)));
		Assert.assertEquals(positions - 1, indexer.getIdx((0xFFFFFFFFFFFFFFFFL >>> fpBits)));
		
		// Correctly wraps around when end of array is reached
		Assert.assertEquals(0, indexer.getIdx((0xFFFFFFFFFFFFFFFFL >>> fpBits), 1));
		// Correctly wraps around when end of array is reached twice
		Assert.assertEquals(0, indexer.getIdx((0xFFFFFFFFFFFFFFFFL >>> fpBits), (int)positions+1));
	}

	@Test
	public void testRescaleMaximum() throws RemoteException {
		final int fpBits = 1;
		final long positions = 11L;
		
		final Indexer indexer = new OffHeapDiskFPSet.Indexer(positions, fpBits, 11L);

		// indexer spreads over all positions
		Assert.assertEquals(0, indexer.getIdx(1));
		Assert.assertEquals(10, indexer.getIdx(11));
		
		// Correctly wraps around when end of array is reached
		Assert.assertEquals(0, indexer.getIdx(11, 1));
	}
	
	@Test
	public void testBitshiftOvershoot() throws RemoteException {
		final int fpBits = 1;
		final long positions = 536870912L;
		
		final Indexer indexer = new OffHeapDiskFPSet.BitshiftingIndexer(positions, fpBits);
		Assert.assertEquals(0, indexer.getIdx(9223371952792813846L, 5));
	}
	
	private void doTest(final int fpBits, final long positions, final int logPos, final Indexer indexer) {
		Assert.assertTrue(Double.compare(Math.pow(2, logPos - fpBits), positions) == 0);
		
		Assert.assertEquals(fpBits, Long.numberOfLeadingZeros((positions << (Long.SIZE - logPos)) - 1));
		
		for (long l = 0; l < positions; l++) {
			final long fp = l << (Long.SIZE - logPos);
			Assert.assertEquals(l, indexer.getIdx(fp));
			final long fpNext = ((l+1L) << (Long.SIZE - logPos)) - 1;
			Assert.assertEquals(l, indexer.getIdx(fpNext));
		}
		Assert.assertEquals(0, indexer.getIdx(positions << (Long.SIZE - logPos)));
	}
}
