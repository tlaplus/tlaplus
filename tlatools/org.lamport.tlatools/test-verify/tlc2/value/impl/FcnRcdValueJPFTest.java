/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved. 
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
package tlc2.value.impl;

import org.junit.Test;

import gov.nasa.jpf.util.test.TestJPF;

/**
 * Uses {@link DataRaceDetector} to check that two workers can apply
 * the same shared function without a data race.
 * <p>
 * TLC 1.8 built an index the first time a function with more than ten domain
 * elements was applied ({@code FcnRcdValue#createIndex}), and published it in
 * its own synchronized block, while {@link FcnRcdValue#select(Value)} read the
 * index and its entries without a lock. At 425dc60aa, this test reports races
 * on {@code indexTbl} between {@code createIndex} and {@code select}.
 * <p>
 * JPF runs threads under sequential consistency, so it finds the race but not
 * its effect. {@code createIndex} writes the entries of the index before it
 * assigns {@code indexTbl}, and under sequential consistency every worker that
 * sees {@code indexTbl} also sees the entries. The Java memory model lets a
 * worker that reads {@code indexTbl} without a lock see it before the entries.
 * If an entry is still -1, {@code select} fails with "not in the domain of the
 * function". JPF also does not report the entries, because no other worker can
 * reach them while they are written.
 * <p>
 * See <a href="https://github.com/tlaplus/tlaplus/issues/439">#439</a>.
 */
public class FcnRcdValueJPFTest extends TestJPF {

	private static final String[] JPF_ARGS = { "+listener=tlc2.value.impl.DataRaceDetector",
			"+race.include=tlc2.*",
			// Also schedule at array reads and writes to find races on array elements.
			"+cg.threads.break_arrays=true" };

	private static final int N = 16;

	public static void main(String[] args) {
		new FcnRcdValueJPFTest().testSelect();
	}

	@Test
	public void testSelect() {
		if (verifyNoPropertyViolation(JPF_ARGS)) {
			final Value[] domain = new Value[N];
			final Value[] values = new Value[N];
			for (int i = 0; i < N; i++) {
				domain[i] = IntValue.gen(i);
				values[i] = IntValue.gen(100 + i);
			}
			final FcnRcdValue fcn = new FcnRcdValue(domain, values, true);

			final Thread w1 = new Thread(new Worker(fcn), "Worker1");
			final Thread w2 = new Thread(new Worker(fcn), "Worker2");
			w1.start();
			w2.start();
			try {
				w1.join();
				w2.join();
			} catch (InterruptedException e) {
				Thread.currentThread().interrupt();
			}
		}
	}

	private static final class Worker implements Runnable {
		private final FcnRcdValue fcn;

		Worker(final FcnRcdValue fcn) {
			this.fcn = fcn;
		}

		@Override
		public void run() {
			final int v = ((IntValue) fcn.select(IntValue.gen(0))).val;
			if (v != 100) {
				throw new AssertionError("f[0] = " + v);
			}
		}
	}
}
