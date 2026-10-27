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
 * The sets S == {{2}, {1}} and T == {{4}, {3}}, whose elements are not
 * normalized. A worker that evaluates T \in S while another worker evaluates
 * S \in T must still finish. Searching S for T compares T with the elements of
 * S, which sorts T, and vice versa. If a worker holds the lock of S while it
 * searches S, the two workers may deadlock.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class SetEnumValueDeadlockTest extends ValueLincheckTestCase {

	private final SetEnumValue s;

	private final SetEnumValue t;

	public SetEnumValueDeadlockTest() {
		this(set(set(2), set(1)), set(set(4), set(3)));
	}

	private SetEnumValueDeadlockTest(final SetEnumValue s, final SetEnumValue t) {
		this.s = s;
		this.t = t;
	}

	// {k}
	private static SetEnumValue set(final int k) {
		return new SetEnumValue(new Value[] { IntValue.gen(k) }, false);
	}

	// {e1, e2}
	private static SetEnumValue set(final Value e1, final Value e2) {
		return new SetEnumValue(new Value[] { e1, e2 }, false);
	}

	@Override
	protected Value value() {
		return s;
	}

	@Operation
	public boolean tInS() {
		return s.member(t);
	}

	@Operation
	public boolean sInT() {
		return t.member(s);
	}

	// A random scenario rarely looks up S and T in each other before a
	// fingerprint normalizes them.
	@Override
	@Test
	public void modelChecking() {
		modelCheckingParallel("tInS", "sInT");
	}
}
