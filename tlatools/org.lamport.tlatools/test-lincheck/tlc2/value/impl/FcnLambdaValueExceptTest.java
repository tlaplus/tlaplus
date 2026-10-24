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

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.SemanticNode;
import tlc2.tool.EvalControl;
import tlc2.tool.TLCStates;
import tlc2.util.Context;
import util.UniqueString;

/**
 * The function f == [[x \in 1..3 |-> 7] EXCEPT ![2] = 99]. A worker that
 * evaluates f[2] while another worker fingerprints f must still get 99.
 * Fingerprinting converts f to a FcnRcdValue. If FcnLambdaValue#toFcnRcd
 * publishes the FcnRcdValue before it applies the EXCEPT, the first worker may
 * get 7.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class FcnLambdaValueExceptTest extends ValueLincheckTestCase {

	private final FcnLambdaValue fcn;

	public FcnLambdaValueExceptTest() {
		this(except(new FcnLambdaValue(
				new FcnParams(
						new FormalParamNode[][] { { new FormalParamNode(UniqueString.of("x"), 0,
								SyntaxTreeNode.nullSTN, null, null) } },
						new boolean[] { false }, new Value[] { new IntervalValue(1, 3) }),
				SemanticNode.nullSN, evaluatingTo(IntValue.gen(7)), Context.Empty, TLCStates.createDummyState(),
				null, EvalControl.Clear)));
	}

	private static FcnLambdaValue except(final FcnLambdaValue fcn) {
		return (FcnLambdaValue) fcn.takeExcept(new ValueExcept(new Value[] { IntValue.gen(2) }, IntValue.gen(99)));
	}

	private FcnLambdaValueExceptTest(final FcnLambdaValue fcn) {
		super(fcn);
		this.fcn = fcn;
	}

	@Operation
	public int select() {
		return ((IntValue) fcn.select(IntValue.gen(2))).val;
	}

	@Test
	public void fingerPrintAndSelect() {
		modelCheckingParallel("fingerPrint", "select");
	}
}
