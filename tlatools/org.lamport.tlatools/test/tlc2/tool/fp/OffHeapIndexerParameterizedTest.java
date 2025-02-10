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
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import tlc2.tool.fp.OffHeapDiskFPSet.Indexer;

@RunWith(Parameterized.class)
public abstract class OffHeapIndexerParameterizedTest {

	// Round down to the specified number of positions to the nearest multiple that
	// requires a 1024MB allocation.
	public static long roundHalfEven(long l) {
		final long MULTIPLE = 8L * 1024 * 1024 * 1024;
		return (l / MULTIPLE) * MULTIPLE;
	}

	@Parameters(name = "positions: {0}, fpBits: {1}")
	public static Collection<Object[]> data() {
		final List<Object[]> p = new ArrayList<>(21762);

		for (int fpBits = 1; fpBits > 0; fpBits--) {
			for (int i = 1; i < 32; i++) {
				for (int j = 2; j < 32; j++) {
					p.add(new Object[] { roundHalfEven(Long.MAX_VALUE >>> j) + (i * (1L << 30)), fpBits });
				}
			}

			for (int k = 1 << 7; k > 0; k--) {
				p.add(new Object[] { k * (1L << 27), fpBits });
			}

			for (int posBits = 63 - fpBits; posBits > 16; posBits--) {
				p.add(new Object[] { 1L << posBits, fpBits });
			}
		}
		return p;
	}

	@Parameter(0)
	public long positions;
	@Parameter(1)
	public int fpBits;

	protected abstract Indexer getIndexer();

	@Test
	public void testZero() {
		Assert.assertEquals(0, getIndexer().getIdx(0L));
	}

	@Test
	public void testOne() {
		Assert.assertEquals(0, getIndexer().getIdx(1L));
	}

	@Test
	public void testLongMin() {
		// -1 >>> fpBits
		final long highFP = 0xFFFFFFFFFFFFFFFFL >>> fpBits;
		Assert.assertEquals(positions - 1L, getIndexer().getIdx(highFP));
	}

	@Test
	public void testLongMax() {
		// 0xFFFFFFFFFFFFFFFFL & 0x7FFFFFFFFFFFFFFFL >>> fpBits
		// -1 & 0x7FFFFFFFFFFFFFFFL >>> fpBits
		final long highFP = Long.MAX_VALUE >>> fpBits;
		Assert.assertEquals((positions / 2L) - 1L, getIndexer().getIdx(highFP));
	}
	
	@Test
	public void testSome() {
		// Check N fps uniformly distributed in the range [lower,upper].
		final long upper = Long.MAX_VALUE >>> fpBits;
		final int N = 1 << 10;
		final long step = upper / N;
		
		long l = 0;
		for (int i = 0; i < Math.min(N, upper); i++) {
			final long h = i * step;
			Assert.assertTrue(getIndexer().getIdx(l) <= getIndexer().getIdx(h));
			l = h;
		}
	}
}
