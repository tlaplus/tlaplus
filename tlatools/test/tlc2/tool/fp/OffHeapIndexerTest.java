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
		final int bucketCapacity = 1;
		final long positions = 128L;
		final int logPos = 8;
		doTest(fpBits, positions, logPos, new OffHeapDiskFPSet.BitshiftingIndexer(bucketCapacity, positions, fpBits));
	}

	@Test
	public void testRescale() throws RemoteException {
		final int fpBits = 1;
		final int bucketCapacity = 1;
		final long positions = 128L;
		final int logPos = 8;
		doTest(fpBits, positions, logPos, new OffHeapDiskFPSet.Indexer(bucketCapacity, positions, fpBits));
	}

	@Test
	public void testBitshifting2() throws RemoteException {
		final int fpBits = 2;
		final int bucketCapacity = 1;
		final long positions = 128L;
		final int logPos = 9;
		doTest(fpBits, positions, logPos, new OffHeapDiskFPSet.BitshiftingIndexer(bucketCapacity, positions, fpBits));
	}

	@Test
	public void testRescale2() throws RemoteException {
		final int fpBits = 2;
		final int bucketCapacity = 1;
		final long positions = 128L;
		final int logPos = 9;
		doTest(fpBits, positions, logPos, new OffHeapDiskFPSet.Indexer(bucketCapacity, positions, fpBits));
	}

	private void doTest(final int fpBits, final long positions, final int logPos, final Indexer indexer) {
		Assert.assertTrue(Double.compare(Math.pow(2, logPos - fpBits), positions) == 0);
		
		Assert.assertEquals(fpBits, Long.numberOfLeadingZeros((positions << (Long.SIZE - logPos)) - 1));
		
		for (long l = 0; l < positions; l++) {
			final long fp = l << (Long.SIZE - logPos);
			Assert.assertEquals(l, indexer.getLogicalPosition(fp));
			final long fpNext = ((l+1L) << (Long.SIZE - logPos)) - 1;
			Assert.assertEquals(l, indexer.getLogicalPosition(fpNext));
		}
		Assert.assertEquals(0, indexer.getLogicalPosition(positions << (Long.SIZE - logPos)));
	}
}
