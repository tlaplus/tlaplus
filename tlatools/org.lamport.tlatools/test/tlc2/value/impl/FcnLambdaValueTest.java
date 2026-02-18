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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertSame;

import java.lang.reflect.InvocationHandler;
import java.lang.reflect.Proxy;

import org.junit.Test;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.EvalControl;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStates;
import tlc2.util.Context;
import tlc2.util.FP64;
import util.UniqueString;

public class FcnLambdaValueTest {

	private static ITool mockIToolReturning(final Value evalResult) {
		return (ITool) Proxy.newProxyInstance(ITool.class.getClassLoader(), new Class<?>[] { ITool.class },
				(InvocationHandler) (proxy, method, args) -> {
					if ("eval".equals(method.getName())) {
						return evalResult;
					}
					throw new UnsupportedOperationException("test mock: " + method.getName());
				});
	}

	private static FormalParamNode dummyFormal(String name) {
		return new FormalParamNode(UniqueString.uniqueStringOf(name), 0, SyntaxTreeNode.nullSTN, null, null);
	}

	/** FcnParams for [x \in 1..n |-> body]: one formal, non-tuple, domain 1..n. */
	private static FcnParams singleParamDomain(Value domain) {
		final FormalParamNode[][] formals = new FormalParamNode[][] { { dummyFormal("x") } };
		final boolean[] isTuples = new boolean[] { false };
		final Value[] domains = new Value[] { domain };
		return new FcnParams(formals, isTuples, domains);
	}

	private static FcnLambdaValue createFcnLambda(Value domain, Value val) {
		final FcnParams params = singleParamDomain(domain);
		final SemanticNode body = SemanticNode.nullSN;
		final TLCState state = TLCStates.createDummyState();
		return new FcnLambdaValue(params, body, mockIToolReturning(val), Context.Empty, state, null, EvalControl.Clear);
	}

	@Test
	public void testToString() {
		// TLA+: f == [x \in 1..2 |-> 42]
		FcnLambdaValue flv = createFcnLambda(new IntervalValue(1, 2), IntValue.gen(42));
		// TLA+: ToString(f) = <<42, 42>>
		assertEquals("<<42, 42>>", flv.toString());

		// TLA+: g == [x \in {"a", "b"} |-> 42]
		flv = createFcnLambda(new SetEnumValue(new Value[] { new StringValue("a"), new StringValue("b") }, false),
				IntValue.gen(42));
		// TLA+: ToString(g) = [a |-> 42, b |-> 42]
		assertEquals("[a |-> 42, b |-> 42]", flv.toString());
	}

	@Test
	public void testToFcnRcd() {
		// TLA+: f == [x \in 1..2 |-> 42]
		FcnLambdaValue flv = createFcnLambda(new IntervalValue(1, 2), IntValue.gen(42));
		// TLA+: f converted to explicit function record/tuple: <<42, 42>>
		assertEquals("<<42, 42>>", flv.toFcnRcd().toString());

		// TLA+: g == [x \in {"a", "b"} |-> 42]
		flv = createFcnLambda(new SetEnumValue(new Value[] { new StringValue("a"), new StringValue("b") }, false),
				IntValue.gen(42));
		// TLA+: g converted to explicit function record: [a |-> 42, b |-> 42]
		assertEquals("[a |-> 42, b |-> 42]", flv.toFcnRcd().toString());
	}

	@Test
	public void testSelectAndApply() {
		// TLA+: f == [x \in 1..3 |-> 7]
		final FcnLambdaValue flv = createFcnLambda(new IntervalValue(1, 3), IntValue.gen(7));
		// TLA+: f[1] = 7 /\ f[2] = 7 /\ f[3] = 7
		assertEquals(IntValue.gen(7), flv.select(IntValue.gen(1)));
		assertEquals(IntValue.gen(7), flv.select(IntValue.gen(2)));
		assertEquals(IntValue.gen(7), flv.apply(IntValue.gen(3), EvalControl.Clear));
		assertEquals("7", flv.select(IntValue.gen(1)).toString());
		assertEquals("7", flv.apply(IntValue.gen(3), EvalControl.Clear).toString());
		assertEquals("<<7, 7, 7>>", flv.toString());
	}

	@Test
	public void testTakeExceptOverridesValue() {
		// TLA+: base == [x \in 1..3 |-> 7]
		final FcnLambdaValue base = createFcnLambda(new IntervalValue(1, 3), IntValue.gen(7));
		// TLA+: updated == [base EXCEPT ![2] = 99]
		final ValueExcept ex = new ValueExcept(new Value[] { IntValue.gen(2) }, IntValue.gen(99));
		final FcnLambdaValue updated = (FcnLambdaValue) base.takeExcept(ex);

		// TLA+: updated[2] = 99 /\ updated[1] = 7 /\ updated[3] = 7
		assertEquals(IntValue.gen(7), updated.select(IntValue.gen(1)));
		assertEquals(IntValue.gen(99), updated.select(IntValue.gen(2)));
		assertEquals(IntValue.gen(7), updated.select(IntValue.gen(3)));
		assertEquals("<<7, 7, 7>>", base.toString());
		assertEquals("<<7, 99, 7>>", updated.toString());
	}

	@Test
	public void testDomainIsStableAcrossConversion() {
		// TLA+: f == [x \in 1..2 |-> 42]
		final FcnLambdaValue flv = createFcnLambda(new IntervalValue(1, 2), IntValue.gen(42));
		// TLA+: DOMAIN f = 1..2, both before and after forcing record conversion.
		assertEquals(new IntervalValue(1, 2), flv.getDomain());
		assertEquals("1..2", flv.getDomain().toString());
		assertEquals("<<42, 42>>", flv.toFcnRcd().toString());
		assertEquals(new IntervalValue(1, 2), flv.getDomain());
		assertEquals("1..2", flv.getDomain().toString());
	}

	@Test
	public void testToFcnRcdReturnsCachedInstance() {
		// TLA+: f == [x \in 1..2 |-> 42]
		final FcnLambdaValue flv = createFcnLambda(new IntervalValue(1, 2), IntValue.gen(42));
		// Same semantic value after repeated conversion.
		final Value first = flv.toFcnRcd();
		final Value second = flv.toFcnRcd();
		assertSame(first, second);
		assertEquals("<<42, 42>>", first.toString());
		assertEquals("<<42, 42>>", second.toString());
	}

	@Test
	public void testToRcdForIntervalDomainIsNull() {
		// TLA+: f == [x \in 1..2 |-> 42]
		final FcnLambdaValue flv = createFcnLambda(new IntervalValue(1, 2), IntValue.gen(42));
		// TLA+: not a record with string-field domain; toRcd is undefined/null.
		assertNull(flv.toRcd());
	}

	@Test
	public void testToRcdForStringDomain() {
		// TLA+: r == [x \in {"a", "b"} |-> 5]
		final FcnLambdaValue flv = createFcnLambda(
				new SetEnumValue(new Value[] { new StringValue("a"), new StringValue("b") }, false), IntValue.gen(5));
		// TLA+: r can be interpreted as a record: [a |-> 5, b |-> 5]
		assertEquals("[a |-> 5, b |-> 5]", flv.toString());
		assertEquals("[a |-> 5, b |-> 5]", flv.toRcd().toString());
	}

	@Test
	public void testFingerprintStableAcrossConversion() {
		// TLA+: f == [x \in 1..3 |-> 9]
		final FcnLambdaValue intervalFcn = createFcnLambda(new IntervalValue(1, 3), IntValue.gen(9));
		assertEquals("<<9, 9, 9>>", intervalFcn.toString());
		final long fpIntervalBefore = intervalFcn.fingerPrint(0L);
		// Conversion path 1: symbolic -> explicit function record.
		assertEquals("<<9, 9, 9>>", intervalFcn.toFcnRcd().toString());
		// Conversion path 2: symbolic/record -> string rendering.
		assertEquals("<<9, 9, 9>>", intervalFcn.toString());
		// Conversion path 3: toRcd is not available for non-string domains.
		assertNull(intervalFcn.toRcd());
		final long fpIntervalAfter = intervalFcn.fingerPrint(0L);
		assertEquals(fpIntervalBefore, fpIntervalAfter);

		// TLA+: r == [x \in {"a", "b"} |-> 9]
		final FcnLambdaValue stringFcn = createFcnLambda(
				new SetEnumValue(new Value[] { new StringValue("a"), new StringValue("b") }, false), IntValue.gen(9));
		assertEquals("[a |-> 9, b |-> 9]", stringFcn.toString());
		final long fpStringBefore = stringFcn.fingerPrint(0L);
		// Conversion path 1: symbolic -> explicit function record.
		assertEquals("[a |-> 9, b |-> 9]", stringFcn.toFcnRcd().toString());
		// Conversion path 2: function -> record value.
		assertEquals("[a |-> 9, b |-> 9]", stringFcn.toRcd().toString());
		// Conversion path 3: render after conversions.
		assertEquals("[a |-> 9, b |-> 9]", stringFcn.toString());
		final long fpStringAfter = stringFcn.fingerPrint(0L);
		assertEquals(fpStringBefore, fpStringAfter);
	}

	@Test
	public void testTakeExceptThenConvertToFcnRcd() {
		// TLA+: base == [x \in 1..2 |-> 1]
		final FcnLambdaValue base = createFcnLambda(new IntervalValue(1, 2), IntValue.gen(1));
		// TLA+: updated == [base EXCEPT ![1] = 8]
		final FcnLambdaValue updated = (FcnLambdaValue) base
				.takeExcept(new ValueExcept(new Value[] { IntValue.gen(1) }, IntValue.gen(8)));
		// TLA+: updated converted form is <<8, 1>>
		assertEquals("<<8, 1>>", updated.toFcnRcd().toString());
	}

	@Test
	public void testToFcnRcdAssertFail() {
		final FcnLambdaValue base = createFcnLambda(new IntervalValue(1, 2), IntValue.gen(42));

		// v1 = [v EXCEPT ![1] = 99]
		final ValueExcept ex1 = new ValueExcept(new Value[] { IntValue.gen(1) }, IntValue.gen(99));
		final FcnLambdaValue flv1 = (FcnLambdaValue) base.takeExcept(ex1);

		// v2 = [v1 EXCEPT ![2] = 100]
		final ValueExcept ex2 = new ValueExcept(new Value[] { IntValue.gen(2) }, IntValue.gen(100));
		final FcnLambdaValue flv2 = (FcnLambdaValue) flv1.takeExcept(ex2);

		flv1.toFcnRcd();
		// util.Assert$TLCRuntimeException: Attempted to apply EXCEPT construct to the
		// integer 99.
		flv2.toFcnRcd();

		assertEquals(IntValue.gen(99), flv1.select(IntValue.gen(1)));
		assertEquals(IntValue.gen(42), flv1.select(IntValue.gen(2)));
		assertEquals(IntValue.gen(99), flv2.select(IntValue.gen(1)));
		assertEquals(IntValue.gen(100), flv2.select(IntValue.gen(2)));
	}

	@Test
	public void testToFcnRcdClassCastException() {
		final FcnLambdaValue base = createFcnLambda(new IntervalValue(1, 2), IntValue.gen(42));

		// v1 = [v EXCEPT ![1] = 99]
		final ValueExcept ex1 = new ValueExcept(new Value[] { IntValue.gen(1) }, IntValue.gen(99));
		final FcnLambdaValue flv1 = (FcnLambdaValue) base.takeExcept(ex1);

		// v2 = [v1 EXCEPT ![2] = 100]
		final ValueExcept ex2 = new ValueExcept(new Value[] { IntValue.gen(2) }, IntValue.gen(100));
		final FcnLambdaValue flv2 = (FcnLambdaValue) flv1.takeExcept(ex2);

		flv2.toFcnRcd();
		// java.lang.ClassCastException: class tlc2.value.impl.IntValue cannot be cast
		// to class tlc2.value.impl.FcnRcdValue (tlc2.value.impl.IntValue and
		// tlc2.value.impl.FcnRcdValue ...
		flv1.toFcnRcd();

		assertEquals(IntValue.gen(99), flv1.select(IntValue.gen(1)));
		assertEquals(IntValue.gen(42), flv1.select(IntValue.gen(2)));
		assertEquals(IntValue.gen(99), flv2.select(IntValue.gen(1)));
		assertEquals(IntValue.gen(100), flv2.select(IntValue.gen(2)));
	}

	@Test
	public void testToFcnRcdSilentCorruption() {
		// TLA+: Base body returns a function: [j \in {1, 2} |-> 0]
		final FcnRcdValue defaultFcn = new FcnRcdValue(new IntervalValue(1, 2),
				new Value[] { IntValue.gen(0), IntValue.gen(0) }, null);

		// TLA+: Base == [i \in 1..2 |-> defaultFcn]
		final FcnLambdaValue base = createFcnLambda(new IntervalValue(1, 2), defaultFcn);

		// TLA+: val1 == [j \in {1, 2} |-> 10 + j] = <<11, 12>>
		final FcnRcdValue val1 = new FcnRcdValue(new IntervalValue(1, 2),
				new Value[] { IntValue.gen(11), IntValue.gen(12) }, null);
		// TLA+: x == [Base EXCEPT ![1] = val1]
		final ValueExcept ex1 = new ValueExcept(new Value[] { IntValue.gen(1) }, val1);
		final FcnLambdaValue flv1 = (FcnLambdaValue) base.takeExcept(ex1);

		// TLA+: val2 == [j \in {1, 2} |-> 20 + j] = <<21, 22>>
		final FcnRcdValue val2 = new FcnRcdValue(new IntervalValue(1, 2),
				new Value[] { IntValue.gen(21), IntValue.gen(22) }, null);
		// TLA+: y == [x EXCEPT ![2] = val2]
		final ValueExcept ex2 = new ValueExcept(new Value[] { IntValue.gen(2) }, val2);
		final FcnLambdaValue flv2 = (FcnLambdaValue) flv1.takeExcept(ex2);

		assertEquals("<<<<11, 12>>, <<0, 0>>>>", flv1.toFcnRcd().toString());
		// <<11, <<21, 22>>>> without bugfix, i.e, creating fresh ValueEx instances in
		// FcnLambdaValue#toFcnRcd.
		assertEquals("<<<<11, 12>>, <<21, 22>>>>", flv2.toFcnRcd().toString());
	}

	@Test
	public void testToFcnRcdSilentCorruptionFP() {
		// TLA+: Base body returns a function: [j \in {1, 2} |-> 0]
		final FcnRcdValue defaultFcn = new FcnRcdValue(new IntervalValue(1, 2),
				new Value[] { IntValue.gen(0), IntValue.gen(0) }, null);

		// TLA+: Base == [i \in 1..2 |-> defaultFcn]
		final FcnLambdaValue base = createFcnLambda(new IntervalValue(1, 2), defaultFcn);

		// TLA+: val1 == [j \in {1, 2} |-> 10 + j] = <<11, 12>>
		final FcnRcdValue val1 = new FcnRcdValue(new IntervalValue(1, 2),
				new Value[] { IntValue.gen(11), IntValue.gen(12) }, null);
		// TLA+: x == [Base EXCEPT ![1] = val1]
		final ValueExcept ex1 = new ValueExcept(new Value[] { IntValue.gen(1) }, val1);
		final FcnLambdaValue flv1 = (FcnLambdaValue) base.takeExcept(ex1);

		// TLA+: val2 == [j \in {1, 2} |-> 20 + j] = <<21, 22>>
		final FcnRcdValue val2 = new FcnRcdValue(new IntervalValue(1, 2),
				new Value[] { IntValue.gen(21), IntValue.gen(22) }, null);
		// TLA+: y == [x EXCEPT ![2] = val2]
		final ValueExcept ex2 = new ValueExcept(new Value[] { IntValue.gen(2) }, val2);
		final FcnLambdaValue flv2 = (FcnLambdaValue) flv1.takeExcept(ex2);

		flv1.toFcnRcd();
		final Value fcnRcd = flv2.toFcnRcd();

		// Freshly create the correct y as a concrete record:
		// TLA+: [1 |-> val1, 2 |-> val2]
		final FcnRcdValue freshY = new FcnRcdValue(new IntervalValue(1, 2), new Value[] { val1, val2 }, null);

		// fcnRcd hashes to the same fp as a freshly created correct record.
		FP64.Init();
		assertEquals(freshY.fingerPrint(0L), fcnRcd.fingerPrint(0L));
	}
}
