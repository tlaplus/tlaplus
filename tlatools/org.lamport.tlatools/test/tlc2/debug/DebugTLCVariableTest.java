/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved. 
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
package tlc2.debug;

import static org.junit.Assert.assertEquals;

import java.util.List;
import java.util.Random;

import org.junit.Test;

import tlc2.module.Strings;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.TLCVariable;
import tlc2.value.impl.TupleValue;

public class DebugTLCVariableTest {
	private static final Random rnd = new Random();

	@Test
	public void testFiniteEmptySetValue() {
		assertEquals(0, new DebugTLCVariable("4711").setInstance(new SetEnumValue()).getNested(rnd).size());
	}

	@Test
	public void testFiniteSetValue() {
		List<TLCVariable> outer = new DebugTLCVariable("4711").setInstance(new SetEnumValue(new SetEnumValue()))
				.getNested(rnd);
		assertEquals(1, outer.size());
		assertEquals(0, outer.get(0).getNested(rnd).size());
	}

	@Test
	public void testFiniteNestedValue() {
		List<TLCVariable> vars = new DebugTLCVariable("4711")
				.setInstance(new SetEnumValue(new SetEnumValue(new TupleValue(IntValue.ValZero, IntValue.ValOne))))
				.getNested(rnd);
		assertEquals(1, vars.size());

		vars = vars.get(0).getNested(rnd);
		assertEquals(1, vars.size());

		vars = vars.get(0).getNested(rnd);
		assertEquals(2, vars.size());

		for (TLCVariable var : vars) {
			assertEquals(0, var.getNested(rnd).size());
		}
	}

	@Test
	public void testInfiniteValue() {
		assertEquals(0, new DebugTLCVariable("4711").setInstance(Strings.STRING()).getNested(rnd).size());
	}
}
