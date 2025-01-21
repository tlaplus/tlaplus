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

	@Parameter(0)
	public long pBits;
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
		Assert.assertEquals((1L << pBits) - 1L, getIndexer().getIdx(highFP));
	}

	@Test
	public void testLongMax() {
		// 0xFFFFFFFFFFFFFFFFL & 0x7FFFFFFFFFFFFFFFL >>> fpBits
		// -1 & 0x7FFFFFFFFFFFFFFFL >>> fpBits
		final long highFP = Long.MAX_VALUE >>> fpBits;
		Assert.assertEquals(((1L << pBits) / 2L) - 1L, getIndexer().getIdx(highFP));
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
