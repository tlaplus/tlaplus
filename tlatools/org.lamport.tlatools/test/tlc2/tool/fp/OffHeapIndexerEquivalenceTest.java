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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import tlc2.tool.fp.OffHeapDiskFPSet.Indexer;

@RunWith(Parameterized.class)
public class OffHeapIndexerEquivalenceTest {

	@Parameters(name = "posBits: {0}, fpBits: {1}, fp: {2}, offset: {3}")
	public static Collection<Object[]> data() {
		final List<Object[]> p = new ArrayList<>(242048);
		for (int fpBits = 1; fpBits < 63; fpBits++) {
			for (int pBits = 62 - fpBits; pBits > 0; pBits--) {
				for (int b = 63 - fpBits; b > 0; b--) {
					p.add(new Object[] { pBits, fpBits, b, -1 });
					p.add(new Object[] { pBits, fpBits, b, 0 });
					p.add(new Object[] { pBits, fpBits, b, 1 });
				}
				p.add(new Object[] { pBits, fpBits, 0, 0 });
				p.add(new Object[] { pBits, fpBits, 0, 1 });
			}
		}
		return p;
	}

	private final long positions;
	private final int fpBits;
	private final long fp;

	public OffHeapIndexerEquivalenceTest(final long pBits, final int fpBits, final int fpBitIdx, final int offset) {
		this.positions = 1L << pBits;
		this.fpBits = fpBits;
		this.fp = (1L << fpBitIdx) + offset;
	}

	@Test
	public void testInfiniteBitshifting() {
		Assume.assumeTrue(Long.bitCount(positions) == 1);
		
		final Indexer iIndexer = new OffHeapDiskFPSet.InfinitePrecisionIndexer(positions, fpBits);
		final Indexer bIndexer = new OffHeapDiskFPSet.BitshiftingIndexer(positions, fpBits);

		Assert.assertEquals(iIndexer.getIdx(fp), bIndexer.getIdx(fp));
	}
}
