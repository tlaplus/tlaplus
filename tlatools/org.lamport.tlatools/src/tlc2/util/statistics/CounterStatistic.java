/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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

import java.util.concurrent.atomic.LongAdder;
import java.util.function.BooleanSupplier;

public abstract class CounterStatistic {
	
	public static CounterStatistic getInstance(final BooleanSupplier s) {
		if (s.getAsBoolean()) {
			return new LongAdderCounterStatistic();
		} else {
			return new NoopCounterStatistic();
		}
	}
	
	public abstract void increment();
	
	public abstract void add(final long evalCount);

	public abstract long getCount();

	private CounterStatistic() {
		// private ctor
	}

	private static class NoopCounterStatistic extends CounterStatistic {
		
		@Override
		public final long getCount() {
			return 0;
		}
		
		@Override
		public final void increment() {
			// noop
		}
		
		@Override
		public void add(long evalCount) {
			// noop
		}
	}
	
	private static class LongAdderCounterStatistic extends CounterStatistic {

		private final LongAdder adder = new LongAdder();

		@Override
		public final long getCount() {
			return this.adder.sum();
		}

		@Override
		public final void increment() {
			adder.increment();
		}

		@Override
		public void add(long evalCount) {
			adder.add(evalCount);
		}

		@Override
		public String toString() {
			return adder.toString();
		}
	}
}
