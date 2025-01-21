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
import java.util.concurrent.ThreadLocalRandom;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import tlc2.tool.fp.OffHeapDiskFPSet.BitshiftingIndexer;
import tlc2.tool.fp.OffHeapDiskFPSet.Indexer;
import tlc2.tool.fp.OffHeapDiskFPSet.InfinitePrecisionIndexer;

@RunWith(Parameterized.class)
public class OffHeapIndexerEquivalenceTest {

	@Parameters(name = "positions: {0}, fpBits: {1}, fp: 1L<<{2}")
	public static Collection<Object[]> data() {
		final List<Object[]> p = new ArrayList<>();

		for (int fpBits = 1; fpBits > 0; fpBits--) {
			for (int k = 50; k > 0; k--) {
				for (int b = 62; b > 48; b--) {
					p.add(new Object[] { k * 134_217_728L, fpBits, b });
				}
			}
			
			for (int posBits = 63 - fpBits; posBits > 16; posBits--) { 
				for (int b = 62; b > 42; b--) {
					p.add(new Object[] { 1L << posBits, fpBits, b });
				}
			}
		}
		return p;
	}

	@Parameter(0)
	public long positions;
	@Parameter(1)
	public int fpBits;
	@Parameter(2)
	public int fpRangeBit;

	@Test
	public void testInfiniteBitshifting() {
		Assume.assumeTrue(Long.bitCount(positions) == 1);
		
		final Indexer iIndexer = new InfinitePrecisionIndexer(positions, fpBits);
		final Indexer bIndexer = new BitshiftingIndexer(positions, fpBits);

		doTest(iIndexer, bIndexer);
	}

	private void doTest(final Indexer expected, final Indexer actual) {
		final long upperBound = 1L << fpRangeBit;

		final int N = 1 << 10;
		
		// Check N fps randomly generated number in the range [lower,upper).
		final long lowerBound = 1L << (fpRangeBit - 1);
		for (int i = 0; i < Math.min(N, upperBound - lowerBound); i++) {
			// TODO No need for ThreadLocalRandom.current() with Java 17 because 17 has
			// RandomGenerator has nextLong(long, long)
			final long fp = ThreadLocalRandom.current().nextLong(lowerBound, upperBound);
			Assert.assertEquals(expected.getIdx(fp), actual.getIdx(fp));
			Assert.assertTrue(actual.getIdx(fp+1) >= actual.getIdx(fp));
		}

		// Check N fps uniformly distributed in the range [lower,upper].
		final long step = (upperBound - lowerBound) / N;
		for (int i = 0; i < Math.min(N, upperBound - lowerBound); i++) {
			final long fp = lowerBound + i * step;
			Assert.assertEquals(expected.getIdx(fp), actual.getIdx(fp));
			Assert.assertEquals(expected.getIdx(fp+1), actual.getIdx(fp+1));
			Assert.assertTrue(actual.getIdx(fp) <= actual.getIdx(fp+1));
		}

		// Check N fps around the upper bound.
		for (long l = 1L; l < N && upperBound + l <= Long.MAX_VALUE; l++) {
			final long fp = upperBound + l;
			Assert.assertEquals(expected.getIdx(fp), actual.getIdx(fp));
			Assert.assertTrue(actual.getIdx(fp) >= actual.getIdx(fp-1));
		}
		for (long l = 1L; l < N && upperBound - l >= 0L; l++) {
			final long fp = upperBound - l;
			Assert.assertEquals(expected.getIdx(fp), actual.getIdx(fp));
			Assert.assertTrue(actual.getIdx(fp) <= actual.getIdx(fp+1));
		}

		// Check fp given by junit parameter.
		Assert.assertEquals(expected.getIdx(upperBound), actual.getIdx(upperBound));
}
