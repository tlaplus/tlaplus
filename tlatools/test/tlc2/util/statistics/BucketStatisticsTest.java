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

package tlc2.util.statistics;

import tlc2.util.statistics.BucketStatistics;
import junit.framework.TestCase;

public class BucketStatisticsTest extends TestCase {
	
	public void testInvalidArgument() {
		try {
			final BucketStatistics gs = new BucketStatistics();
			gs.addSample(-1);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail();
	}
	
	public void testMean() {
		final BucketStatistics gs = new BucketStatistics();
		assertEquals(-1.0d, gs.getMean());

		gs.addSample(0);
		assertEquals(0.0d, gs.getMean());
		
		gs.addSample(1);
		gs.addSample(2);
		assertEquals(1.0d, gs.getMean());

		gs.addSample(2);
		gs.addSample(2);
		assertEquals(1.4d, gs.getMean());
	}

	public void testMedian() {
		final BucketStatistics gs = new BucketStatistics();
		assertEquals(-1, gs.getMedian());

		gs.addSample(0);
		assertEquals(0, gs.getMedian());
		
		gs.addSample(1);
		gs.addSample(2);
		assertEquals(1, gs.getMedian());

		gs.addSample(2);
		gs.addSample(2);
		assertEquals(2, gs.getMedian());
	}

	public void testMin() {
		final BucketStatistics gs = new BucketStatistics();
		assertEquals(-1, gs.getMin());

		gs.addSample(0);
		gs.addSample(0);
		gs.addSample(0);
		gs.addSample(1);
		gs.addSample(1);
		gs.addSample(2);
		gs.addSample(2);
		gs.addSample(2);
		assertEquals(0, gs.getMin());
	}
	
	public void testMax() {
		final BucketStatistics gs = new BucketStatistics();
		assertEquals(-1, gs.getMax());

		gs.addSample(0);
		gs.addSample(0);
		gs.addSample(0);
		gs.addSample(1);
		gs.addSample(1);
		gs.addSample(2);
		gs.addSample(2);
		gs.addSample(2);
		gs.addSample(2);
		gs.addSample(3);
		assertEquals(3, gs.getMax());
	}

	public void testStandardDeviation() {
		final BucketStatistics gs = new BucketStatistics();
		assertEquals(-1.0, gs.getStdDev());

		gs.addSample(0);
		gs.addSample(0);
		gs.addSample(0);
		gs.addSample(1);
		gs.addSample(1);
		gs.addSample(2);
		gs.addSample(2);
		gs.addSample(2);
		gs.addSample(2);
		gs.addSample(3);
		assertEquals(1.005d, (Math.round(gs.getStdDev() * 10000d) / 10000d));
	}

	public void testGetPercentile() {
		final BucketStatistics gs = new BucketStatistics();
		assertEquals(-1.0, gs.getPercentile(1));
		
		try {
			gs.addSample(1); // <- first element
			gs.getPercentile(1.1);
			gs.getPercentile(-0.1);
		} catch (Exception e) {
			fail(e.getMessage());
		}
		
		gs.addSample(1);
		gs.addSample(1);
		gs.addSample(2); // <- 0.5 percentile
		gs.addSample(2);
		gs.addSample(2);
		gs.addSample(3);
		assertEquals(2.0d, gs.getPercentile(0.5d));
		assertEquals(2.0d, gs.getPercentile(0.75d));
		assertEquals(3.0d, gs.getPercentile(0.999d));
	}
	// NaN test
	public void testGetPercentileNaN() {
		try {
			final BucketStatistics gs = new BucketStatistics();
			gs.getPercentile(Double.NaN);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail("Parameter not a number");
	}
	
	public void testToString() {
		try {
			//just invoke to check for exceptions
			final BucketStatistics gs = new BucketStatistics();
			gs.toString();
			
			gs.addSample(0);
			gs.addSample(0);
			gs.addSample(0);
			gs.addSample(1);
			gs.addSample(1);
			gs.addSample(2);
			gs.addSample(2);
			gs.addSample(2);
			gs.addSample(2);
			gs.addSample(3);
			gs.toString();
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}
}