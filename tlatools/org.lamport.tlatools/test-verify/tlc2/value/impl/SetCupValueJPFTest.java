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
 * Uses {@link DataRaceDetector} to check that two workers can share
 * S \cup T without a data race. The publisher calls
 * {@link SetCupValue#size()}, which caches the enumerated union in
 * {@code cupSet}; the reader calls {@link SetCupValue#toSetEnum()}, which
 * returns the cache.
 * <p>
 * In TLC 1.8, {@code SetCupValue#convertAndCache} assigned {@code cupSet}
 * without a lock if it was null, and in a second synchronized block if it was
 * {@link SetEnumValue#DummyEnum}, which {@link SetCupValue#deepNormalize()} put
 * there; {@code toSetEnum} read it without a lock. At 425dc60aa, both tests
 * report races on {@code cupSet}. {@link #testSizeAndToSetEnum()} also reports
 * the two workers sorting the cached set in place at the same time
 * (<a href="https://github.com/tlaplus/tlaplus/issues/1445">#1445</a>).
 * <p>
 * JPF runs threads under sequential consistency, so it finds the races but not
 * their effect: a worker that sees the cache but not its elements.
 * <p>
 * See <a href="https://github.com/tlaplus/tlaplus/issues/439">#439</a>.
 */
public class SetCupValueJPFTest extends TestJPF {

	private static final String[] JPF_ARGS = { "+listener=tlc2.value.impl.DataRaceDetector",
			"+race.include=tlc2.*",
			// Also schedule at array reads and writes to find races on array elements.
			"+cg.threads.break_arrays=true" };

	public static void main(String[] args) {
		new SetCupValueJPFTest().testSizeAndToSetEnum();
		new SetCupValueJPFTest().testSizeAndToSetEnumDeepNormalized();
	}

	@Test
	public void testSizeAndToSetEnum() {
		if (verifyNoPropertyViolation(JPF_ARGS)) {
			run(false);
		}
	}

	@Test
	public void testSizeAndToSetEnumDeepNormalized() {
		if (verifyNoPropertyViolation(JPF_ARGS)) {
			run(true);
		}
	}

	private static void run(final boolean deepNormalize) {
		final SetEnumValue s = new SetEnumValue(new Value[] { IntValue.gen(1), IntValue.gen(2), IntValue.gen(3) },
				true);
		final SetEnumValue t = new SetEnumValue(new Value[] { IntValue.gen(4), IntValue.gen(5) }, true);
		final SetCupValue cup = new SetCupValue(s, t);
		if (deepNormalize) {
			cup.deepNormalize();
		}

		final Thread publisher = new Thread(new Runnable() {
			@Override
			public void run() {
				final int n = cup.size();
				if (n != 5) {
					throw new AssertionError("publisher: |S \\cup T| = " + n);
				}
			}
		}, "Publisher");
		final Thread reader = new Thread(new Runnable() {
			@Override
			public void run() {
				final int n = ((SetEnumValue) cup.toSetEnum()).elems.size();
				if (n != 5) {
					throw new AssertionError("reader: |S \\cup T| = " + n);
				}
			}
		}, "Reader");
		publisher.start();
		reader.start();
		try {
			publisher.join();
			reader.join();
		} catch (InterruptedException e) {
			Thread.currentThread().interrupt();
		}
	}
}
