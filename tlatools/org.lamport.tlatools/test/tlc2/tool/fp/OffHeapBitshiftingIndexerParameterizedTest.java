/*******************************************************************************
 * Copyright (c) 2025 Microsoft Research. All rights reserved. 
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
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import tlc2.tool.fp.OffHeapDiskFPSet.Indexer;

@RunWith(Parameterized.class)
public class OffHeapBitshiftingIndexerParameterizedTest {

	@Parameters(name = "pos: {0}, fpBits: {1}")
	public static Collection<Object[]> data() {
		final List<Object[]> p = new ArrayList<>();
		for (int fpBits = 1; fpBits < 64; fpBits++) {
			for (int pBits = 63 - fpBits; pBits > 0; pBits--) {
				p.add(new Object[] { pBits, fpBits });
			}
		}
		return p;
	}

	private final long positions;
	private final int fpBits;

	public OffHeapBitshiftingIndexerParameterizedTest(final long pBits, final int fpBits) {
		this.positions = 1L << pBits;
		this.fpBits = fpBits;
	}

	@Test
	public void testZero() throws RemoteException {
		final Indexer indexer = new OffHeapDiskFPSet.BitshiftingIndexer(positions, fpBits);
		Assert.assertEquals(0, indexer.getIdx(0L));
		Assert.assertEquals(0, indexer.getIdx(1L));
	}

	@Test
	public void testOne() throws RemoteException {
		Assert.assertEquals(0, new OffHeapDiskFPSet.BitshiftingIndexer(positions, fpBits).getIdx(1L));
	}

	@Test
	public void testLongMin() throws RemoteException {
		final long highFP = 0xFFFFFFFFFFFFFFFFL >>> fpBits;
		Assert.assertEquals(positions - 1L, new OffHeapDiskFPSet.BitshiftingIndexer(positions, fpBits).getIdx(highFP));
	}

	@Test
	public void testLongMax() throws RemoteException {
		final long highFP = Long.MAX_VALUE >>> fpBits;
		Assert.assertEquals((positions / 2L) - 1L, new OffHeapDiskFPSet.BitshiftingIndexer(positions, fpBits).getIdx(highFP));
	}
}
