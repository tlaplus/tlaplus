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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;

import tlc2.module.AnySet;
import tlc2.module.Integers;
import tlc2.module.Naturals;
import tlc2.module.Sequences;
import tlc2.module.Strings;
import util.Assert.TLCRuntimeException;
import util.UniqueString;

/**
 * SetOfFcnsValue, SetOfRcdsValue, and SetOfTuplesValue short-circuit their
 * equals on Value#isEmpty, so a wrong answer makes TLC report two distinct
 * sets as equal. ValueTest.tla states what TLC must answer, proved with TLAPS.
 *
 * The values below are built in Java, rather than asserted in TLA+ as
 * test-model/EmptySetEqCases.tla does, because TLC reduces a set expression to
 * a SetEnumValue as soon as it can. An assumption reaches the \cup, the \, and
 * the UNION branch of isEmpty only with an operand that TLC cannot enumerate,
 * such as {"d1"} \cup Nat, and it never reaches the \cap branch: a \cap with
 * one enumerable operand is intersected on the spot (Reducible#cap), and one
 * without raises an error instead of answering.
 *
 * https://github.com/tlaplus/tlaplus/issues/1407
 */
public class ValueTest {

	private static final Value ONE = IntValue.gen(1);
	private static final Value TWO = IntValue.gen(2);

	private static final SetEnumValue set() {
		return new SetEnumValue();
	}

	private static final SetEnumValue set(final Value v) {
		return new SetEnumValue(new Value[] { v }, true);
	}

	private static final SetOfRcdsValue rcds(final Value field) {
		return new SetOfRcdsValue(new UniqueString[] { UniqueString.uniqueStringOf("n1") },
				new Value[] { field }, false);
	}

	@Test
	public void testIsEmpty() {
		assertTrue("{}", set().isEmpty());
		assertFalse("{1}", set(ONE).isEmpty());

		assertTrue("1..0", new IntervalValue(1, 0).isEmpty());
		assertFalse("1..1", new IntervalValue(1, 1).isEmpty());

		assertTrue("{1} \\cap {2}", new SetCapValue(set(ONE), set(TWO)).isEmpty());
		assertFalse("{1} \\cap {1}", new SetCapValue(set(ONE), set(ONE)).isEmpty());

		assertTrue("{} \\cup {}", new SetCupValue(set(), set()).isEmpty());
		assertFalse("{} \\cup {1}", new SetCupValue(set(), set(ONE)).isEmpty());

		assertTrue("{1} \\ {1}", new SetDiffValue(set(ONE), set(ONE)).isEmpty());
		assertFalse("{1} \\ {2}", new SetDiffValue(set(ONE), set(TWO)).isEmpty());

		assertTrue("[{1} -> {}]", new SetOfFcnsValue(set(ONE), set()).isEmpty());
		assertFalse("[{} -> {}] denotes {<<>>}", new SetOfFcnsValue(set(), set()).isEmpty());

		assertTrue("[n1: {}]", rcds(set()).isEmpty());
		assertFalse("[n1: {1}]", rcds(set(ONE)).isEmpty());

		assertTrue("{} \\X {1}", new SetOfTuplesValue(set(), set(ONE)).isEmpty());
		assertFalse("{1} \\X {1}", new SetOfTuplesValue(set(ONE), set(ONE)).isEmpty());

		assertFalse("SUBSET {} denotes {{}}", new SubsetValue(set()).isEmpty());
		assertFalse("SUBSET {1}", new SubsetValue(set(ONE)).isEmpty());

		assertTrue("UNION {}", new UnionValue(set()).isEmpty());
		assertTrue("UNION {{}}", new UnionValue(set(set())).isEmpty());
		assertFalse("UNION {{1}}", new UnionValue(set(set(ONE))).isEmpty());

		// SETPREDVALUE is missing, and no assumption covers it either: a
		// SetPredValue needs the parsed predicate of a spec, which JUnit
		// cannot easily supply.

		// isEmpty refuses an overridden value until the commit that lets each
		// module answer for itself, which uncomments the four assertions.
//		assertFalse("Nat", Naturals.Nat().isEmpty());
//		assertFalse("Int", Integers.Int().isEmpty());
//		assertFalse("STRING", Strings.STRING().isEmpty());
//		assertFalse("Seq({})", Sequences.Seq(set()).isEmpty());

		try {
			AnySet.ANY().isEmpty();
			fail("isEmpty answered for ANY, whose elements TLA+ leaves unspecified");
		} catch (TLCRuntimeException e) {
			// Expected.
		}

		try {
			ONE.isEmpty();
			fail("isEmpty answered for 1, whose elements TLA+ leaves unspecified");
		} catch (TLCRuntimeException e) {
			// Expected.
		}
	}
}
