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
 * The functions f == ((2 :> 2) :> 1 @@ (1 :> 1) :> 2) and
 * g == ((4 :> 4) :> 1 @@ (3 :> 3) :> 2), whose domains are not normalized. A
 * worker that evaluates f[g] while another worker evaluates g[f] must still
 * finish. Searching the domain of f for g compares g with the elements of the
 * domain, which sorts g, and vice versa. If a worker holds the lock of f while
 * it searches the domain of f, the two workers may deadlock.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class FcnRcdValueDeadlockTest extends ValueLincheckTestCase {

	private final FcnRcdValue f;

	private final FcnRcdValue g;

	public FcnRcdValueDeadlockTest() {
		this(fcn(fcn(2), fcn(1)), fcn(fcn(4), fcn(3)));
	}

	private FcnRcdValueDeadlockTest(final FcnRcdValue f, final FcnRcdValue g) {
		this.f = f;
		this.g = g;
	}

	// k :> k
	private static FcnRcdValue fcn(final int k) {
		return new FcnRcdValue(new Value[] { IntValue.gen(k) }, new Value[] { IntValue.gen(k) }, false);
	}

	// d1 :> 1 @@ d2 :> 2
	private static FcnRcdValue fcn(final Value d1, final Value d2) {
		return new FcnRcdValue(new Value[] { d1, d2 }, new Value[] { IntValue.gen(1), IntValue.gen(2) }, false);
	}

	@Override
	protected Value value() {
		return f;
	}

	@Operation
	public boolean fOfG() {
		return f.select(g) != null;
	}

	@Operation
	public boolean gOfF() {
		return g.select(f) != null;
	}

	// A random scenario rarely looks up f and g in each other before a
	// fingerprint normalizes them.
	@Override
	@Test
	public void modelChecking() {
		modelCheckingParallel("fOfG", "gOfF");
	}
}
