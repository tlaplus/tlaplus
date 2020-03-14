/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved. 
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
import java.util.NavigableMap;

import javax.management.NotCompliantMBeanException;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.management.TLCStandardMBean;
import tlc2.util.statistics.management.BucketStatisticsMXWrapper;

public abstract class AbstractBucketStatistics implements IBucketStatistics {

	/**
	 * Human readable statistics name (used in toString())
	 */
	protected final String title;

	public AbstractBucketStatistics(String aTitle) {
		super();
		this.title = aTitle;
	}

	/**
	 * @param aTitle
	 *            A title for console pretty printing
	 * @param pkg
	 *            A package name for this statistics, e.g. tlc2.tool.liveness
	 *            for stats are from classes in the liveness package.
	 * @param name
	 *            The (class) name of the source of the statistics.
	 */
	public AbstractBucketStatistics(final String aTitle, final String pkg, final String name) {
		this(aTitle);
		try {
			//TODO unregister somehow
			new BucketStatisticsMXWrapper(this, name, pkg);
		} catch (NotCompliantMBeanException e) {
			// not expected to happen would cause JMX to be broken, hence just log and
			// continue
			MP.printWarning(
					EC.GENERAL,
					"Failed to create MBean wrapper for BucketStatistics. No statistics/metrics will be avaiable.",
					e);
			TLCStandardMBean.getNullTLCStandardMBean();
		}
	}

	public String toString() {
		final StringBuffer buf = new StringBuffer();
		buf.append("============================%n");
		buf.append("=" + title + "=%n");
		buf.append("============================%n");
		buf.append(String.format("Observations: %d%n", getObservations()));
		buf.append(String.format("Min: %d%n", getMin()));
		buf.append(String.format("Max: %d%n", getMax()));
		buf.append(String.format("Mean: %.2f%n", getMean()));
		buf.append(String.format("Median: %d%n", getMedian()));
		buf.append(String.format("Standard deviation: %.2f%n", getStdDev()));
		buf.append(String.format("75%%: %.2f%n", getPercentile(0.75d)));
		buf.append(String.format("95%%: %.2f%n", getPercentile(0.95d)));
		buf.append(String.format("98%%: %.2f%n", getPercentile(0.98d)));
		buf.append(String.format("99%%: %.2f%n", getPercentile(0.99d)));
		buf.append(String.format("99.9%%: %.2f%n", getPercentile(0.999d)));
		buf.append("numEdges/occurrences (log scale)%n");
		buf.append("--------------------------------%n");
		final Iterator<Entry<Integer, Long>> iterator = getSamples().entrySet().iterator();
		while(iterator.hasNext()) {
			Entry<Integer, Long> next = iterator.next();
			long amount = next.getValue();
			int i = next.getKey();
			buf.append(String.format("%02d", i));
			buf.append(":");
			buf.append(String.format("%02d", amount));
			buf.append(" ");
			for (int j = 0; j < Math.log(amount); j++) {
				buf.append("#");
			}
			buf.append("%n");
		}
		buf.append("============================");
		return buf.toString();
	}

	public int getMedian() {
		long l = getObservations();
		if (l <= 0) {
			return -1;
		}
		// skip forward for as many elements as 1/2 observations. The 
		// corresponding bucket is the median.
		long sum = 0L;
		final Iterator<Entry<Integer, Long>> iterator = getSamples().entrySet().iterator();
		while(iterator.hasNext()) {
			final Entry<Integer, Long> next = iterator.next();
			sum += next.getValue();
			if (sum > (l / 2)) {
				return next.getKey();
			}
		}
		// make compiler happy
		throw new RuntimeException("bug, shoud not get here");
	}

	public double getMean() {
		long sum = 0L;
		// Sum up values and count
		final Iterator<Entry<Integer, Long>> iterator = getSamples().entrySet().iterator();
		while(iterator.hasNext()) {
			final Entry<Integer, Long> next = iterator.next();
			final long value = next.getValue();
			final int i = next.getKey();
			sum += value * i;
		}
		if (getObservations() > 0) {
			return (sum / (getObservations() * 1.0d));
		} else {
			// No mean yet
			return -1;
		}
	}

	public int getMin() {
		if (getObservations() <= 0) {
			return -1;
		}
		return getSamples().firstKey();
	}

	public int getMax() {
		if (getObservations() <= 0) {
			return -1;
		}
		return getSamples().lastKey();
	}

	public double getStdDev() {
		final long N = getObservations();
		if (N <= 0) {
			return -1.0d;
		}
		final double mean = getMean() * 1.0d;
		double sum = 0.0d;
		final Iterator<Entry<Integer, Long>> iterator = getSamples().entrySet().iterator();
		while(iterator.hasNext()) {
			Entry<Integer, Long> next = iterator.next();
			double Xi = next.getKey() * 1.0d;
			double diff = Xi - mean;
			sum += (diff * diff) * ((next.getValue() * 1.0d)); // diff^2
		}
		double variance = sum / (N * 1.0d);
		double stdDev = Math.sqrt(variance);
		return stdDev;
	}

	public double getPercentile(double quantile) {
		if (Double.isNaN(quantile)) {
			throw new IllegalArgumentException("NaN");
		}
		final long obsv = getObservations();
		if (obsv <= 0) {
			return -1.0;
		}
		// adjust values to valid range
		quantile = Math.min(1.0, quantile);
		quantile = Math.max(0, quantile);
		
		final NavigableMap<Integer, Long> samples = getSamples();

		// calculate the elements position for the
		// given quantile
	    final int pos = (int) ((obsv * 1.0d) * quantile);
		if (pos > obsv) {
	    	return samples.size();
	    }
	    if (pos < 0) {
	    	return 0;
	    }
	    
	    // advance to the bucket at position
	    long cnt = 0l;
		final Iterator<Entry<Integer, Long>> iterator = samples.entrySet().iterator();
		while(iterator.hasNext()) {
			Entry<Integer, Long> next = iterator.next();
			int i  = next.getKey();
			cnt += next.getValue();
			if (cnt > pos) {
				return i;
			}
		}
		return quantile;
	}

}