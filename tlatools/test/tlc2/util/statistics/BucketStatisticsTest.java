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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;
import tlc2.util.statistics.BucketStatistics;

public class BucketStatisticsTest {
	
	@Test
	public void testInvalidArgument() {
		try {
			final IBucketStatistics gs = new BucketStatistics();
			gs.addSample(-1);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail();
	}
	
	@Test
	public void testMean() {
		final IBucketStatistics gs = new BucketStatistics();
		assertTrue(Double.compare(-1.0d, gs.getMean()) == 0);

		gs.addSample(0);
		assertTrue(Double.compare(0.0d, gs.getMean()) == 0);
		
		gs.addSample(1);
		gs.addSample(2);
		assertTrue(Double.compare(1.0d, gs.getMean()) == 0);

		gs.addSample(2);
		gs.addSample(2);
		assertTrue(Double.compare(1.4d, gs.getMean()) == 0);
	}

	@Test
	public void testMedian() {
		final IBucketStatistics gs = new BucketStatistics();
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

	@Test
	public void testMin() {
		final IBucketStatistics gs = new BucketStatistics();
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
	
	@Test
	public void testMax() {
		final IBucketStatistics gs = new BucketStatistics();
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

	@Test
	public void testStandardDeviation() {
		final IBucketStatistics gs = new BucketStatistics();
		assertEquals(-1.0, gs.getStdDev(), 0);

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
		assertTrue(Double.compare(1.005d, (Math.round(gs.getStdDev() * 10000d) / 10000d)) == 0);
	}

	@Test
	public void testGetPercentile() {
		final IBucketStatistics gs = new BucketStatistics();
		assertEquals(-1.0, gs.getPercentile(1), 0);
		
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
		assertTrue(Double.compare(2.0d, gs.getPercentile(0.5d)) == 0);
		assertTrue(Double.compare(2.0d, gs.getPercentile(0.5d)) == 0);
		assertTrue(Double.compare(2.0d, gs.getPercentile(0.75d)) == 0);
		assertTrue(Double.compare(3.0d, gs.getPercentile(0.999d)) == 0);
	}
	// NaN test
	@Test
	public void testGetPercentileNaN() {
		try {
			final IBucketStatistics gs = new BucketStatistics();
			gs.getPercentile(Double.NaN);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail("Parameter not a number");
	}
	
	@Test
	public void testToString() {
		try {
			//just invoke to check for exceptions
			final IBucketStatistics gs = new BucketStatistics();
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
	
	@Test
	public void testMaximum() {
		final IBucketStatistics gs = new BucketStatistics("test title", 8);
		gs.addSample(16);
		gs.addSample(16);
		gs.addSample(16);
		assertEquals(8, gs.getMedian());
		assertEquals(3, gs.getObservations());
	}
}