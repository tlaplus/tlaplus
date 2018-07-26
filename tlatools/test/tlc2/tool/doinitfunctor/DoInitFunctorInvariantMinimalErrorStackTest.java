/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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
package tlc2.tool.doinitfunctor;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class DoInitFunctorInvariantMinimalErrorStackTest extends ModelCheckerTestCase {

	public DoInitFunctorInvariantMinimalErrorStackTest() {
		super("DoInitFunctorMinimalErrorStack", "DoInitFunctor");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "1", "1", "1"));
		assertFalse(recorder.recorded(EC.GENERAL));

		assertTrue(recorder.recordedWithStringValues(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE,
				"public static tlc2.value.BoolValue tlc2.module.Naturals.GEQ(tlc2.value.Value,tlc2.value.Value)",
				"The first argument of > should be an integer, but instead it is:\n" + 
				"<<1, 1>>"));

		String errorStack = "0. Line 8, column 3 to line 9, column 13 in DoInitFunctorMinimalErrorStack\n"
				+ "1. Line 8, column 6 to line 8, column 25 in DoInitFunctorMinimalErrorStack\n"
				+ "2. Line 9, column 6 to line 9, column 13 in DoInitFunctorMinimalErrorStack\n"
				+ "3. Line 14, column 8 to line 14, column 13 in DoInitFunctorMinimalErrorStack\n\n";
		assertTrue(recorder.recordedWithStringValue(EC.TLC_NESTED_EXPRESSION, errorStack));
	}
}
