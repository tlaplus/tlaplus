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
import static org.junit.Assert.fail;

import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

@RunWith(Parameterized.class)
public class FixedSizedBucketStatisticsTest {

	@SuppressWarnings("rawtypes")
	@Parameterized.Parameters
	public static Collection<Class> bucketStatistics() {
		return Arrays.asList(
				new Class[] { FixedSizedConcurrentBucketStatistics.class, FixedSizedBucketStatistics.class });
	}

	private final IBucketStatistics bucketStatistic;

	@SuppressWarnings({ "rawtypes", "unchecked" })
	public FixedSizedBucketStatisticsTest(Class bucketStatistic) throws InstantiationException, IllegalAccessException,
			IllegalArgumentException, InvocationTargetException, NoSuchMethodException, SecurityException {
		this.bucketStatistic = (IBucketStatistics) bucketStatistic.getConstructor(String.class, int.class)
				.newInstance("FixedSizedBucketStatisticsTest", 8);
	}
	
	@Test
	public void testMin() {
		assertEquals(-1, bucketStatistic.getMin());

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
	public void testInvalidArgument() {
		try {
			bucketStatistic.addSample(-1);
		} catch (IllegalArgumentException e) {
			return;
		}
		fail();
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
	public void testMaximum() {
		bucketStatistic.addSample(16);
		bucketStatistic.addSample(16);
		bucketStatistic.addSample(16);
		assertEquals(7, bucketStatistic.getMax());
		assertEquals(7, bucketStatistic.getMedian());
		assertEquals(3, bucketStatistic.getObservations());
	}
}