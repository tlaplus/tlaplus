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

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

/**
 * The functions a == (2 :> 2 @@ 1 :> 1) and b == (4 :> 4 @@ 3 :> 3), whose
 * domains are not normalized, are shared by the functions
 * f == (a :> 1 @@ b :> 2) and g == (b :> 1 @@ a :> 2), and, through the sets
 * {a} and {b}, by m == ({a} :> 1 @@ {b} :> 2) and n == ({b} :> 1 @@ {a} :> 2).
 * Workers that sort f, g, m, n, and a concurrently must all finish.
 * <p>
 * Sorting f holds the lock of f while it compares a with b, which sorts a and b
 * under their locks, so the locks nest along the values that contain each
 * other. Sorting g compares b with a. If comparing a with b held the lock of a
 * while it sorted b, a worker that sorts f and a worker that sorts g may
 * deadlock. Comparing {a} with {b} compares a with b, so the locks of m and n
 * nest the same way, with a set, which has no lock, in between.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class FcnRcdValueNestedLockTest extends ValueLincheckTestCase {

	private final FcnRcdValue a;

	private final FcnRcdValue f;

	private final FcnRcdValue g;

	private final SetEnumValue setA;

	private final FcnRcdValue m;

	private final FcnRcdValue n;

	public FcnRcdValueNestedLockTest() {
		this(fcn(IntValue.gen(2), IntValue.gen(1), IntValue.gen(2), IntValue.gen(1)),
				fcn(IntValue.gen(4), IntValue.gen(3), IntValue.gen(4), IntValue.gen(3)));
	}

	private FcnRcdValueNestedLockTest(final FcnRcdValue a, final FcnRcdValue b) {
		this(a, b, new SetEnumValue(new Value[] { a }, false), new SetEnumValue(new Value[] { b }, false));
	}

	private FcnRcdValueNestedLockTest(final FcnRcdValue a, final FcnRcdValue b, final SetEnumValue setA,
			final SetEnumValue setB) {
		this(a, fcn(a, b), fcn(b, a), setA, fcn(setA, setB), fcn(setB, setA));
	}

	private FcnRcdValueNestedLockTest(final FcnRcdValue a, final FcnRcdValue f, final FcnRcdValue g,
			final SetEnumValue setA, final FcnRcdValue m, final FcnRcdValue n) {
		this.a = a;
		this.f = f;
		this.g = g;
		this.setA = setA;
		this.m = m;
		this.n = n;
	}

	// d1 :> v1 @@ d2 :> v2
	private static FcnRcdValue fcn(final Value d1, final Value d2, final Value v1, final Value v2) {
		return new FcnRcdValue(new Value[] { d1, d2 }, new Value[] { v1, v2 }, false);
	}

	// d1 :> 1 @@ d2 :> 2
	private static FcnRcdValue fcn(final Value d1, final Value d2) {
		return fcn(d1, d2, IntValue.gen(1), IntValue.gen(2));
	}

	@Override
	protected Value value() {
		return f;
	}

	@Operation
	public int sortF() {
		return sortAndSelect(f, a);
	}

	@Operation
	public int sortG() {
		return sortAndSelect(g, a);
	}

	@Operation
	public int sortA() {
		return sortAndSelect(a, IntValue.gen(1));
	}

	@Operation
	public int sortM() {
		return sortAndSelect(m, setA);
	}

	@Operation
	public int sortN() {
		return sortAndSelect(n, setA);
	}

	// A random scenario rarely sorts f and g before a fingerprint normalizes them.
	@Override
	@Test
	public void modelChecking() {
		modelCheckingParallel("sortF", "sortG");
	}

	@Test
	public void sortSharedDomainElement() {
		modelCheckingParallel(200_000, "sortF", "sortG", "sortA");
	}

	@Test
	public void sortThroughSets() {
		modelCheckingParallel("sortM", "sortN");
	}

	@Test
	public void sortThroughSetsAndSharedDomainElement() {
		modelCheckingParallel(200_000, "sortM", "sortN", "sortA");
	}
}
