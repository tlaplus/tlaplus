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
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.UniqueString;

public class SequencesTest {

	// Tail("abc") = "bc"
	// TLC can evaluate Tail("abc") because its value, "bc", can be written without
	// explicitly writing any character (characters would be 'b' and 'c', which do 
	// not exist in TLC).
	// https://github.com/tlaplus/tlaplus/issues/512#issuecomment-717602371
	
	@Test
	public void testTailString() {
		Value v = Sequences.Tail(new StringValue("abc"));
		assertTrue(v instanceof StringValue);
		assertEquals(UniqueString.of("bc"), ((StringValue) v).val);
	}

	// Head("a") = "a"[1]  and TLC cannot evaluate "a"[1]:
	// Error evaluating expression: '"abc"[1]'
	// A non-function (a string) was applied as a function.
	
	@Test
	public void testHeadString() {
		try {
			Sequences.Head(new StringValue("a"));
		} catch (EvalException e) {
			assertEquals(EC.TLC_MODULE_ONE_ARGUMENT_ERROR, e.getErrorCode());
			return;
		}
		fail();
	}

	@Test
	public void testHeadStringEmpty() {
		try {
			Sequences.Head(new StringValue(""));
		} catch (EvalException e) {
			assertEquals(EC.TLC_MODULE_ONE_ARGUMENT_ERROR, e.getErrorCode());
			return;
		}
		fail();
	}

	@Test
	public void testAppendString() {
		try {
			Sequences.Append(new StringValue(""), new StringValue("a"));
		} catch (EvalException e) {
			assertEquals(EC.TLC_MODULE_EVALUATING, e.getErrorCode());
			return;
		}
		fail();
	}

	@Test
	public void testAppendString2() {
		try {
			Sequences.Append(new StringValue("abc"), new StringValue("d"));
		} catch (EvalException e) {
			assertEquals(EC.TLC_MODULE_EVALUATING, e.getErrorCode());
			return;
		}
		fail();
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

	// "a" \o <<>> or <<>> \o "a" should produce an error. There is little value in
	// implementing it because concat would only work for the empty sequence.
	
	@Test
	public void testConcatStringToSeq() {
		try {
			Sequences.Concat(new TupleValue(new StringValue("abc")), new StringValue("d"));
		} catch (EvalException e) {
			assertEquals(EC.TLC_MODULE_EVALUATING, e.getErrorCode());
			return;
		}
		fail();
	}

	@Test
	public void testConcatSeqToString() {
		try {
			Sequences.Concat(new StringValue("abc"), new TupleValue(new StringValue("d")));
		} catch (EvalException e) {
			assertEquals(EC.TLC_MODULE_EVALUATING, e.getErrorCode());
			return;
		}
		fail();
	}

	// "a" \o "b" = "ab"
	
	@Test
	public void testConcatStringToString() {
		Value v = Sequences.Concat(new StringValue("abc"), (new StringValue("d")));
		assertTrue(v instanceof StringValue);
		assertEquals(UniqueString.of("abcd"), ((StringValue) v).val);
	}

	@Test
	public void testConcatIntToSeq() {
		try {
			Sequences.Concat(new TupleValue(new StringValue("abc")), IntValue.ValOne);
		} catch (EvalException e) {
			assertEquals(EC.TLC_MODULE_EVALUATING, e.getErrorCode());
			return;
		}
		fail();
	}

	@Test
	public void testConcatSeqToInt() {
		try {
			Sequences.Concat(IntValue.ValOne, new TupleValue(new StringValue("d")));
		} catch (EvalException e) {
			assertEquals(EC.TLC_MODULE_EVALUATING, e.getErrorCode());
			return;
		}
		fail();
	}

	// 1 \o 1 # 11
	
	@Test
	public void testConcatIntToInt() {
		try {
			Sequences.Concat(IntValue.ValOne, IntValue.ValOne);
		} catch (EvalException e) {
			assertEquals(EC.TLC_MODULE_EVALUATING, e.getErrorCode());
			return;
		}
		fail();
	}
	
	// SubSeq("abc", 1, 1) = "a"
	
	@Test
	public void testSubseq() {
		Value v = Sequences.SubSeq(new StringValue("abc"), IntValue.ValOne, IntValue.ValOne);
		assertTrue(v instanceof StringValue);
		assertEquals(UniqueString.of("a"), ((StringValue) v).val);
	}
}
