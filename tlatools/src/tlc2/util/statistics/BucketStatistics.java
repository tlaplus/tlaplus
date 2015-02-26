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

import java.util.Iterator;
import java.util.Map.Entry;
import java.util.concurrent.ConcurrentNavigableMap;
import java.util.concurrent.ConcurrentSkipListMap;
import java.util.concurrent.atomic.AtomicLong;

public class BucketStatistics {
	
	/**
	 * The amount of samples seen by this statistics. It's identical
	 * to the sum of the value of all buckets.
	 */
	protected final AtomicLong observations = new AtomicLong(0);
	
	/**
	 * Instead of using an ever-growing list of samples, identical
	 * samples are counted in a bucket. E.g. the sample 5 is stored
	 * in a bucket with key 5 and a value of 2 if the sample has been
	 * seen two times.
	 * The map is thread safe, so are the values.
	 */
	protected final ConcurrentNavigableMap<Integer, AtomicLong> buckets = new ConcurrentSkipListMap<Integer, AtomicLong>();

	/**
	 * Human readable statistics name (used in toString())
	 */
	private final String title;

	/**
	 * Upper limit for the number of buckets available for sampling. If a sample
	 * exceeds maximum, it will go into the very last bucket. It serves as an
	 * "overflow" bucket.
	 * Useful if samples flatten out to the right and at many buckets with just
	 * a single sample would be added.
	 */
	private final int maximum;

	public BucketStatistics() {
		this("Historgram");
	}
	
	public BucketStatistics(final String aTitle) {
		this(aTitle, Integer.MAX_VALUE);
	}
	
	public BucketStatistics(final String aTitle, final int aMaxmimum) {
		this.title = aTitle;
		this.maximum  = aMaxmimum;
	}
	
	/**
	 * @param amount
	 *            Add a sample to the stastics. Allowed range is 0 <= sample <=
	 *            Integer.MAX_VALUE
	 */
	public void addSample(final int amount) {
		if (amount < 0) {
			throw new IllegalArgumentException("Negative amount invalid");
		}
		
		// If the amount exceeds the fixed maximum, increment the overflow
		// bucket. The overflow bucket is the very last bucket. 
		final int idx = Math.min(maximum, amount);
		
		final AtomicLong atomicLong = buckets.get(idx);
		if(atomicLong == null) {
			buckets.putIfAbsent(idx, new AtomicLong(1));
		} else {
			atomicLong.incrementAndGet();
		}
		observations.getAndIncrement();
	}
	
	/**
	 * @return The sum of all values in all buckets (might exceed int)
	 */
	public long getObservations() {
		return observations.get();
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		final StringBuffer buf = new StringBuffer();
		buf.append("============================\n");
		buf.append("=" + title + "=\n");
		buf.append("============================\n");
		buf.append(String.format("Observations: %d\n", observations.get()));
		buf.append(String.format("Min: %d\n", getMin()));
		buf.append(String.format("Max: %d\n", getMax()));
		buf.append(String.format("Mean: %.2f\n", getMean()));
		buf.append(String.format("Median: %d\n", getMedian()));
		buf.append(String.format("Standard deviation: %.2f\n", getStdDev()));
		buf.append(String.format("75%%: %.2f\n", getPercentile(0.75d)));
		buf.append(String.format("95%%: %.2f\n", getPercentile(0.95d)));
		buf.append(String.format("98%%: %.2f\n", getPercentile(0.98d)));
		buf.append(String.format("99%%: %.2f\n", getPercentile(0.99d)));
		buf.append(String.format("99.9%%: %.2f\n", getPercentile(0.999d)));
		buf.append("numEdges/occurrences (log scale)\n");
		buf.append("--------------------------------\n");
		final Iterator<Entry<Integer, AtomicLong>> iterator = buckets.entrySet().iterator();
		while(iterator.hasNext()) {
			Entry<Integer, AtomicLong> next = iterator.next();
			long amount = next.getValue().get();
			int i = next.getKey();
			buf.append(String.format("%02d", i));
			buf.append(":");
			buf.append(String.format("%02d", amount));
			buf.append(" ");
			for (int j = 0; j < Math.log(amount); j++) {
				buf.append("#");
			}
			buf.append("\n");
		}
		buf.append("============================");
		return buf.toString();
	}

	/**
	 * @return The median
	 */
	int getMedian() {
		long l = observations.get();
		if (l <= 0) {
			return -1;
		}
		// skip forward for as many elements as 1/2 observations. The 
		// corresponding bucket is the median.
		long sum = 0L;
		final Iterator<Entry<Integer, AtomicLong>> iterator = buckets.entrySet().iterator();
		while(iterator.hasNext()) {
			final Entry<Integer, AtomicLong> next = iterator.next();
			sum += next.getValue().get();
			if (sum > (l / 2)) {
				return next.getKey();
			}
		}
		// make compiler happy
		throw new RuntimeException("bug, shoud not get here");
	}

	/**
	 * @return The mean
	 */
	double getMean() {
		long sum = 0L;
		// Sum up values and count
		final Iterator<Entry<Integer, AtomicLong>> iterator = buckets.entrySet().iterator();
		while(iterator.hasNext()) {
			final Entry<Integer, AtomicLong> next = iterator.next();
			final long value = next.getValue().get();
			final int i = next.getKey();
			sum += value * i;
		}
		if (observations.get() > 0) {
			return (sum / (observations.get() * 1.0d));
		} else {
			// No mean yet
			return -1;
		}
	}

	/**
	 * @return The minimum
	 */
	int getMin() {
		if (observations.get() <= 0) {
			return -1;
		}
		return buckets.firstKey();
	}

	/**
	 * @return The maximum
	 */
	int getMax() {
		if (observations.get() <= 0) {
			return -1;
		}
		return buckets.lastKey();
	}

	/**
	 * @return The standard deviation
	 */
	double getStdDev() {
		final long N = observations.get();
		if (N <= 0) {
			return -1.0d;
		}
		final double mean = getMean() * 1.0d;
		double sum = 0.0d;
		final Iterator<Entry<Integer, AtomicLong>> iterator = buckets.entrySet().iterator();
		while(iterator.hasNext()) {
			Entry<Integer, AtomicLong> next = iterator.next();
			double Xi = next.getKey() * 1.0d;
			double diff = Xi - mean;
			sum += (diff * diff) * ((next.getValue().get() * 1.0d)); // diff²
		}
		double variance = sum / (N * 1.0d);
		double stdDev = Math.sqrt(variance);
		return stdDev;
	}

	/**
	 * @param quantile 0 <= d <= 1.0 (adjusted to closet limit if smaller or larger)
	 * @return The given percentile
	 */
	double getPercentile(double quantile) {
		if (Double.isNaN(quantile)) {
			throw new IllegalArgumentException("NaN");
		}
		final long obsv = observations.get();
		if (obsv <= 0) {
			return -1.0;
		}
		// adjust values to valid range
		quantile = Math.min(1.0, quantile);
		quantile = Math.max(0, quantile);
		
		// calculate the elements position for the
		// given quantile
        final int pos = (int) ((obsv * 1.0d) * quantile);
        if (pos > obsv) {
        	return buckets.size();
        }
        if (pos < 0) {
        	return 0;
        }
        
        // advance to the bucket at position
        long cnt = 0l;
		final Iterator<Entry<Integer, AtomicLong>> iterator = buckets.entrySet().iterator();
		while(iterator.hasNext()) {
			Entry<Integer, AtomicLong> next = iterator.next();
			int i  = next.getKey();
			cnt += next.getValue().get();
			if (cnt > pos) {
				return i;
			}
		}
		return quantile;
	}
}
