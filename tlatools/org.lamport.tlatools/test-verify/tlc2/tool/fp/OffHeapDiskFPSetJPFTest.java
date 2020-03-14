/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.BrokenBarrierException;
import java.util.concurrent.atomic.AtomicInteger;

import org.junit.Test;

import gov.nasa.jpf.util.test.TestJPF;

// This class verifies a core part of tlc2.tool.fp.OffHeapDiskFPSet. It is - more or less - a verbatim copy.
public class OffHeapDiskFPSetJPFTest extends TestJPF {
	private static final int PROBE_LIMIT = 2;

	@Test
	public void test() throws InterruptedException, BrokenBarrierException {
		if (verifyNoPropertyViolation("+listener=.listener.AssertionProperty,.listener.ErrorTraceGenerator")) {
			final int size = 3;
			final int max = 3;
			final DummyOffHeapDiskFPSet fpSet = new DummyOffHeapDiskFPSet(size, max);

			// Two concurrent writers.
			for (int i = 0; i < 2; i++) {
				Thread worker = new Thread(new Runnable() {
					public void run() {
						for (long i = 1; i <= max; i++) {
							fpSet.memInsert(i);
						}
					}
				}, "Worker");
				worker.start();
			}
			assert fpSet.checkInvariant() : "FPSet violates its invariant: " + Arrays.toString(fpSet.array.array);
		}
	}
	
	private static class DummyOffHeapDiskFPSet {

		private static final int EMPTY = 0;
		
		private final OffHeapDiskFPSet.Indexer indexer;
		private final DummyLongArray array;
		// AtomicInteger should be LongAdder but JPF fails with what seems to be an
		// internal bug.
		private final AtomicInteger tblCnt;

		public DummyOffHeapDiskFPSet(int positions, long max) {
			this.tblCnt = new AtomicInteger(0);
			this.array = new DummyLongArray(positions);
			this.indexer = new OffHeapDiskFPSet.Indexer(positions, 1, max);
		}

		// This is what we want to verify.
		public boolean memInsert(final long fp) {
			for (int i = 0; i < PROBE_LIMIT; i++) {
				final int position = (int) indexer.getIdx(fp, i);
				final long expected = array.get(position);
				if (expected == EMPTY) {
					if (array.trySet(position, expected, fp)) {
						tblCnt.incrementAndGet();
						return false;
					} else {
						i = i - 1;
						continue;
					}
				}
				if (expected == fp) {
					return true;
				}
			}
			return false;
		}
		
		// Heap-variant of LongArray with synchronized instead of CAS. JPF does
		// not seem to support sun.misc.Unsafe.
		private static class DummyLongArray {
			private final long[] array;
			
			public DummyLongArray(int positions) {
				this.array = new long[positions];
			}

			public long get(int position) {
				return this.array[position];
			}

			public synchronized boolean trySet(int position, long expected, long l) {
				if (this.array[position] == expected) {
					this.array[position] = l;
					return true;
				}
				return false;
			}
		}

		//**** Assertion Helper ****//
		
		public synchronized boolean checkInvariant() {
			// No duplicates.
			int cnt = 0;
			final Set<Long> s = new HashSet<Long>(array.array.length);
			for (int i = 0; i < array.array.length; i++) {
				if (array.array[i] > 0) {
					s.add(array.array[i]);
					cnt++;
				}
			}
			return cnt == s.size();
		}
	}
}
