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
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINbucketStatistic IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package tlc2.util.statistics;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(Parameterized.class)
public class BucketStatisticsTest {

	@SuppressWarnings("rawtypes")
	@Parameterized.Parameters
	public static Collection<Class> bucketStatistics() {
		return Arrays.asList(
				new Class[] { ConcurrentBucketStatistics.class, BucketStatistics.class });
	}

	private final IBucketStatistics bucketStatistic;

	@SuppressWarnings({ "rawtypes", "unchecked" })
	public BucketStatisticsTest(Class bucketStatistic) throws InstantiationException, IllegalAccessException,
			IllegalArgumentException, InvocationTargetException, NoSuchMethodException, SecurityException {
		this.bucketStatistic = (IBucketStatistics) bucketStatistic.getConstructor(String.class)
				.newInstance("BucketStatisticsTest");
	}

	@Test
	public void testInvalidArgument() {
		try {
			bucketStatistic.addSample(-1);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail();
	}

	@Test
	public void testMean() {
		assertTrue(Double.compare(-1.0d, bucketStatistic.getMean()) == 0);

		bucketStatistic.addSample(0);
		assertTrue(Double.compare(0.0d, bucketStatistic.getMean()) == 0);

		bucketStatistic.addSample(1);
		bucketStatistic.addSample(2);
		assertTrue(Double.compare(1.0d, bucketStatistic.getMean()) == 0);

		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		assertTrue(Double.compare(1.4d, bucketStatistic.getMean()) == 0);
	}

	@Test
	public void testMedian() {
		assertEquals(-1, bucketStatistic.getMedian());

		bucketStatistic.addSample(0);
		assertEquals(0, bucketStatistic.getMedian());

		bucketStatistic.addSample(1);
		bucketStatistic.addSample(2);
		assertEquals(1, bucketStatistic.getMedian());

		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		assertEquals(2, bucketStatistic.getMedian());
	}

	@Test
	public void testMin() {
		assertEquals(-1, bucketStatistic.getMin());

		bucketStatistic.addSample(0);
		bucketStatistic.addSample(0);
		bucketStatistic.addSample(0);
		bucketStatistic.addSample(1);
		bucketStatistic.addSample(1);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		assertEquals(0, bucketStatistic.getMin());
	}

	@Test
	public void testMin2() {
		assertEquals(-1, bucketStatistic.getMin());

		bucketStatistic.addSample(1);
		bucketStatistic.addSample(1);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		assertEquals(1, bucketStatistic.getMin());
	}

	@Test
	public void testMax() {
		assertEquals(-1, bucketStatistic.getMax());

		bucketStatistic.addSample(0);
		bucketStatistic.addSample(0);
		bucketStatistic.addSample(0);
		bucketStatistic.addSample(1);
		bucketStatistic.addSample(1);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(3);
		assertEquals(3, bucketStatistic.getMax());
	}

	@Test
	public void testStandardDeviation() {
		assertEquals(-1.0, bucketStatistic.getStdDev(), 0);

		bucketStatistic.addSample(0);
		bucketStatistic.addSample(0);
		bucketStatistic.addSample(0);
		bucketStatistic.addSample(1);
		bucketStatistic.addSample(1);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(3);
		assertTrue(Double.compare(1.005d, (Math.round(bucketStatistic.getStdDev() * 10000d) / 10000d)) == 0);
	}

	@Test
	public void testGetPercentile() {
		assertEquals(-1.0, bucketStatistic.getPercentile(1), 0);

		try {
			bucketStatistic.addSample(1); // <- first element
			bucketStatistic.getPercentile(1.1);
			bucketStatistic.getPercentile(-0.1);
		} catch (Exception e) {
			fail(e.getMessage());
		}

		bucketStatistic.addSample(1);
		bucketStatistic.addSample(1);
		bucketStatistic.addSample(2); // <- 0.5 percentile
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(2);
		bucketStatistic.addSample(3);
		assertTrue(Double.compare(2.0d, bucketStatistic.getPercentile(0.5d)) == 0);
		assertTrue(Double.compare(2.0d, bucketStatistic.getPercentile(0.5d)) == 0);
		assertTrue(Double.compare(2.0d, bucketStatistic.getPercentile(0.75d)) == 0);
		assertTrue(Double.compare(3.0d, bucketStatistic.getPercentile(0.999d)) == 0);
	}

	// NaN test
	@Test
	public void testGetPercentileNaN() {
		try {
			bucketStatistic.getPercentile(Double.NaN);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail("Parameter not a number");
	}

	@Test
	public void testToString() {
		try {
			// just invoke to check for exceptions
			bucketStatistic.toString();

			bucketStatistic.addSample(0);
			bucketStatistic.addSample(0);
			bucketStatistic.addSample(0);
			bucketStatistic.addSample(1);
			bucketStatistic.addSample(1);
			bucketStatistic.addSample(2);
			bucketStatistic.addSample(2);
			bucketStatistic.addSample(2);
			bucketStatistic.addSample(2);
			bucketStatistic.addSample(3);
			bucketStatistic.toString();
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}
}