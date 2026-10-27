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

import tlc2.module.TLC;

/**
 * The function f == (1 :> 10 @@ 2 :> 20 @@ m :> 30), whose domain is not
 * normalized, for the untyped model value m. A worker that evaluates
 * ToString(f) while another worker sorts f must still print f as a function
 * with its values. FcnRcdValue#toString checks whether f is a sequence, which
 * sorts f, unless the check meets m first. With integers only, the check would
 * always sort f before toString prints it. With m, toString may print f while
 * another worker sorts it in place, and pair an element of the domain with the
 * value of another, unless it prints a snapshot.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class TLCToStringFcnTest extends ValueLincheckTestCase {

	static {
		internResults(ValueLincheckTestCase::unsortedMixedFcn, TLC::ToString);
	}

	private final FcnRcdValue fcn = unsortedMixedFcn();

	@Override
	protected Value value() {
		return fcn;
	}

	@Operation
	public String toStringValue() {
		return ((StringValue) TLC.ToString(fcn)).val.toString();
	}

	@Test
	public void fingerPrintAndToStringValue() {
		modelCheckingParallel("fingerPrint", "toStringValue");
	}
}
