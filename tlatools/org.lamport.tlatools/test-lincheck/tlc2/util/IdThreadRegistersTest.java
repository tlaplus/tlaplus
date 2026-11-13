/*******************************************************************************
 * Copyright (c) 2026 Matt Van Horn. All rights reserved.
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
 *   Matt Van Horn - initial API and implementation
 ******************************************************************************/
package tlc2.util;

import java.util.List;

import org.jetbrains.kotlinx.lincheck.Actor;
import org.jetbrains.kotlinx.lincheck.execution.ExecutionScenario;
import org.jetbrains.lincheck.datastructures.ModelCheckingOptions;
import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

import tlc2.value.IValue;
import tlc2.value.impl.IntValue;

/**
 * The registers of an IdThread, which start with four slots. TLCSet in
 * PERIODIC writes them from another thread (Simulator#setAllValues) while
 * the worker writes them too, and TLCGet("all") reads them. A write to a
 * register that the array already holds must not get lost when another
 * write grows the array at the same time.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1486
 */
public class IdThreadRegistersTest {

	private static final int LOW = 1;
	private static final int HIGH = 4;
	private static final int HIGHER = 9;

	private final IdThread thread = new IdThread(0);

	private int get(final int idx) {
		final IValue v = thread.getLocalValue(idx);
		return v == null ? -1 : ((IntValue) v).val;
	}

	@Operation
	public void setLow() {
		thread.setLocalValue(LOW, IntValue.gen(LOW));
	}

	// Grows the array to five slots.
	@Operation
	public void setHigh() {
		thread.setLocalValue(HIGH, IntValue.gen(HIGH));
	}

	// Grows the array to ten slots.
	@Operation
	public void setHigher() {
		thread.setLocalValue(HIGHER, IntValue.gen(HIGHER));
	}

	@Operation
	public int getLow() {
		return get(LOW);
	}

	@Operation
	public int getHigh() {
		return get(HIGH);
	}

	@Operation
	public int getHigher() {
		return get(HIGHER);
	}

	@Operation
	public int countAll() {
		int n = 0;
		for (final IValue v : thread.getLocalValues()) {
			if (v != null) {
				n++;
			}
		}
		return n;
	}

	@Test
	public void setLowWhileGrowing() {
		check(List.of(List.of(actor("setLow")), List.of(actor("setHigh"))));
	}

	@Test
	public void setLowWhileGrowingTwice() {
		check(List.of(List.of(actor("setLow")), List.of(actor("setHigh"), actor("setHigher"))));
	}

	@Test
	public void readWhileGrowing() {
		check(List.of(List.of(actor("setLow"), actor("setHigher")), List.of(actor("getLow"), actor("countAll"))));
	}

	/**
	 * Checks every interleaving of the given workers, after which reading each
	 * register must find every write.
	 */
	private void check(final List<List<Actor>> threads) {
		new ModelCheckingOptions()
			.addCustomScenario(new ExecutionScenario(List.of(), threads,
					List.of(actor("getLow"), actor("getHigh"), actor("getHigher"), actor("countAll")), null))
			.iterations(0)
			.invocationsPerIteration(10_000)
			.check(getClass());
	}

	private static Actor actor(final String operation) {
		try {
			return new Actor(IdThreadRegistersTest.class.getMethod(operation), List.of());
		} catch (NoSuchMethodException e) {
			throw new IllegalArgumentException(e);
		}
	}
}
