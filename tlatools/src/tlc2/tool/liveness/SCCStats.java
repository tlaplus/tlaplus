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

package tlc2.tool.liveness;

import java.util.Map.Entry;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;
import java.util.concurrent.atomic.AtomicLong;

public class SCCStats {

	/**
	 * The number of SCCs found during liveness checking. This is the total
	 * amount over all SCCs found by all concurrent threads (see static). 
	 * It is accessed concurrently, thus use a thread safe implementation.
	 */
	private static final ConcurrentMap<Integer, AtomicLong> stats = new ConcurrentHashMap<Integer, AtomicLong>();
	
	public static void addSCCWithSize(int sizeOfSCC) {
		final AtomicLong atomicLong = stats.get(sizeOfSCC);
		if(atomicLong == null) {
			stats.putIfAbsent(sizeOfSCC, new AtomicLong(1));
		} else {
			atomicLong.incrementAndGet();
		}
	}
	
	public static long getAmountOfSCCs() {
		return stats.size();
	}
	
	public static String print() {
		// Sort the results
		final TreeMap<Integer, AtomicLong> treeMap = new TreeMap<Integer, AtomicLong>(stats);

		// Aggregate results into much smaller map
		final TreeMap<Integer, Long> results = new TreeMap<Integer, Long>();
		for (Entry<Integer, AtomicLong> entry : treeMap.entrySet()) {
			// Null the lowest key bits. This makes multiple keys
			// go into the same "bucket" in the result map.
			//TODO Implement adaptive data aggregation. 0xFFFF0000 is too coarse grained.
			final int key = entry.getKey() & 0xFFFF0000;
			final Long value = entry.getValue().get();
			
			Long curCnt = results.get(key);
			if (curCnt == null) {
				curCnt = 0L;
			}
			curCnt += value;
			results.put(key, curCnt);
		}
		
		// Print
		final StringBuffer buf = new StringBuffer();
		buf.append("======================\n");
		buf.append("=Historgram SCC sizes=\n");
		buf.append("======================\n");
		buf.append("SCC size/occurrences (log scale)\n");
		for (Entry<Integer, Long> itr : results.entrySet()) {
			buf.append(String.format("%08d", itr.getKey()));
			buf.append(":");
			buf.append(String.format("%04d", itr.getValue().longValue()));
			buf.append(" ");
			for (int j = 0; j < Math.log(itr.getValue().longValue()); j++) {
				buf.append("#");
			}
			buf.append("\n");
		}
		buf.append("=======================");
		return buf.toString();
	}
}
