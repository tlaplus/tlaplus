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
package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github179bTest extends ModelCheckerTestCase {

	public Github179bTest() {
		super("Github179b", ExitStatus.FAILURE_SPEC_EVAL);
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));

		assertTrue(recorder.recordedWithStringValues(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE,
				"public static tlc2.value.impl.Value tlc2.module.TLC.Print(tlc2.value.impl.Value,tlc2.value.impl.Value)",
				"Attempted to check equality of integer 1 with non-integer:\n" + 
				"{1}"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_NESTED_EXPRESSION,
				"0. Line 13, column 1 to line 13, column 30 in Github179b\n" + 
				"1. Line 13, column 1 to line 13, column 23 in Github179b\n" + 
				"2. Line 9, column 27 to line 9, column 79 in Github179b\n" + 
				"3. Line 9, column 40 to line 9, column 79 in Github179b\n" + 
				"4. Line 9, column 43 to line 9, column 52 in Github179b\n" + 
				"\n"));
	}
}
