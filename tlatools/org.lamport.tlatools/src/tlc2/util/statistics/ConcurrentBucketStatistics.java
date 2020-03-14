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

import java.util.Map.Entry;
import java.util.NavigableMap;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentNavigableMap;
import java.util.concurrent.ConcurrentSkipListMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.LongAdder;

public class ConcurrentBucketStatistics extends AbstractBucketStatistics implements IBucketStatistics {

	/**
	 * The amount of samples seen by this statistics. It's identical
	 * to the sum of the value of all buckets.
	 */
	private final LongAdder observations = new LongAdder();

	/**
	 * Instead of using an ever-growing list of samples, identical
	 * samples are counted in a bucket. E.g. the sample 5 is stored
	 * in a bucket with key 5 and a value of 2 if the sample has been
	 * seen two times.
	 * The map is thread safe, so are the values.
	 */
	private final ConcurrentNavigableMap<Integer, AtomicLong> buckets = new ConcurrentSkipListMap<Integer, AtomicLong>();
	
	ConcurrentBucketStatistics() {
		super("Concurrent Historgram");
	}
	
	/**
	 * @see {@link BucketStatistics#BucketStatistics(String, int)}
	 */
	public ConcurrentBucketStatistics(final String aTitle) {
		super(aTitle);
	}
	
	/**
	 * @see {@link BucketStatistics#BucketStatistics(String, int, String, String)}
	 */
	public ConcurrentBucketStatistics(final String aTitle, final String pkg, final String name) {
		super(aTitle, pkg, name);
	}
	
	/* (non-Javadoc)
	 * @see tlc2.util.statistics.IBucketStatistics#addSample(int)
	 */
	public void addSample(final int amount) {
		if (amount < 0) {
			throw new IllegalArgumentException("Negative amount invalid");
		}
		
		final AtomicLong atomicLong = buckets.get(amount);
		if(atomicLong == null) {
			buckets.putIfAbsent(amount, new AtomicLong(1));
		} else {
			atomicLong.incrementAndGet();
		}
		observations.increment();
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.AbstractBucketStatistics#getObservations()
	 */
	public long getObservations() {
		return observations.sum();
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.IBucketStatistics#getSamples()
	 */
	public NavigableMap<Integer, Long> getSamples() {
		final NavigableMap<Integer, Long> res = new TreeMap<Integer, Long>();
		for (Entry<Integer, AtomicLong> entry : buckets.entrySet()) {
			res.put(entry.getKey(), entry.getValue().get());
		}
		return res;
	}
}
