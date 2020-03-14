/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved.
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
package tlc2.module;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;

public class SequencesTest {

	@Test
	public void testHeadString() {
		Value a = Sequences.Head(new StringValue("a"));
		assertTrue(a instanceof StringValue);
		assertEquals("a", ((StringValue) a).val.toString());

		a = Sequences.Head(new StringValue("abc"));
		assertTrue(a instanceof StringValue);
		assertEquals("a", ((StringValue) a).val.toString());
	}

	@Test
	public void testHeadStringEmpty() {
		try {
			Sequences.Head(new StringValue(""));
		} catch (EvalException e) {
			assertEquals(EC.TLC_MODULE_APPLY_EMPTY_SEQ, e.getErrorCode());
			return;
		}
		fail();
	}

	@Test
	public void testAppendString() {
		Value a = Sequences.Append(new StringValue(""), new StringValue("a"));
		assertTrue(a instanceof StringValue);
		assertEquals("a", ((StringValue) a).val.toString());

		a = Sequences.Append(new StringValue("abc"), new StringValue("d"));
		assertTrue(a instanceof StringValue);
		assertEquals("abcd", ((StringValue) a).val.toString());
	}

	@Test
	public void testAppendStringNonString() {
		try {
			Sequences.Append(new StringValue(""), IntValue.ValZero);
		} catch (EvalException e) {
			assertEquals(EC.TLC_MODULE_EVALUATING, e.getErrorCode());
			return;
		}
		fail();
	}
}
