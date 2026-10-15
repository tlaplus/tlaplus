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
import util.UniqueString;

/**
 * The records r1 == [f2 |-> a, f1 |-> b] and r2 == [f2 |-> b, f1 |-> a], whose
 * fields are not normalized, hold the functions a == (2 :> 2 @@ 1 :> 1) and
 * b == (4 :> 4 @@ 3 :> 3), whose domains are not normalized either. The
 * functions h == (r1 :> 1 @@ r2 :> 2) and k == (r2 :> 1 @@ r1 :> 2) share r1
 * and r2. Workers that sort h and k, look up r1.f1, and compare r1 with r2
 * concurrently must all finish.
 * <p>
 * Sorting h holds the lock of h while it compares r1 with r2, which sorts r1
 * and r2 under their locks and then compares a with b, which sorts a and b
 * under theirs. Sorting a record compares only the names of its fields, so a
 * worker that holds the lock of a record takes no other lock. If comparing r1
 * with r2 held the lock of r1 while it sorted r2 or compared a with b, a worker
 * that compares r1 with r2 and a worker that compares r2 with r1 may deadlock.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class RecordValueDeadlockTest extends ValueLincheckTestCase {

	private final FcnRcdValue b;

	private final RecordValue r1;

	private final RecordValue r2;

	private final FcnRcdValue h;

	private final FcnRcdValue k;

	public RecordValueDeadlockTest() {
		this(fcn(IntValue.gen(2), IntValue.gen(1), IntValue.gen(2), IntValue.gen(1)),
				fcn(IntValue.gen(4), IntValue.gen(3), IntValue.gen(4), IntValue.gen(3)));
	}

	private RecordValueDeadlockTest(final FcnRcdValue a, final FcnRcdValue b) {
		this(b, rcd(a, b), rcd(b, a));
	}

	private RecordValueDeadlockTest(final FcnRcdValue b, final RecordValue r1, final RecordValue r2) {
		this(b, r1, r2, fcn(r1, r2, IntValue.gen(1), IntValue.gen(2)), fcn(r2, r1, IntValue.gen(1), IntValue.gen(2)));
	}

	private RecordValueDeadlockTest(final FcnRcdValue b, final RecordValue r1, final RecordValue r2,
			final FcnRcdValue h, final FcnRcdValue k) {
		this.b = b;
		this.r1 = r1;
		this.r2 = r2;
		this.h = h;
		this.k = k;
	}

	// d1 :> v1 @@ d2 :> v2
	private static FcnRcdValue fcn(final Value d1, final Value d2, final Value v1, final Value v2) {
		return new FcnRcdValue(new Value[] { d1, d2 }, new Value[] { v1, v2 }, false);
	}

	// [f2 |-> v2, f1 |-> v1]
	private static RecordValue rcd(final Value v2, final Value v1) {
		return new RecordValue(new UniqueString[] { F2, F1 }, new Value[] { v2, v1 }, false);
	}

	@Override
	protected Value value() {
		return h;
	}

	@Operation
	public int sortH() {
		return sortAndSelect(h, r1);
	}

	@Operation
	public int sortK() {
		return sortAndSelect(k, r1);
	}

	@Operation
	public boolean selectR1() {
		return r1.select(new StringValue(F1)) == b;
	}

	@Operation
	public boolean r1EqualsR2() {
		return r1.equals(r2);
	}

	@Operation
	public boolean r2EqualsR1() {
		return r2.equals(r1);
	}

	// A random scenario rarely sorts h and k before a fingerprint normalizes them.
	@Override
	@Test
	public void modelChecking() {
		modelCheckingParallel("sortH", "sortK");
	}

	@Test
	public void sortAndSelectField() {
		modelCheckingParallel("sortH", "selectR1");
	}

	@Test
	public void compareRecords() {
		modelCheckingParallel("r1EqualsR2", "r2EqualsR1");
	}

	@Test
	public void sortAndCompareRecords() {
		modelCheckingParallel(200_000, "sortH", "sortK", "r1EqualsR2");
	}
}
