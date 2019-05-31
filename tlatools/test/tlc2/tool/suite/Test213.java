/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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
package tlc2.tool.suite;

import static org.junit.Assert.assertFalse;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;

public class Test213 extends SuiteETestCase {

	public Test213() {
		super(ExitStatus.ERROR_SPEC_PARSE);
	}
	
	@Test
	public void testSpec() {
		assertFalse(recorder.recorded(EC.GENERAL));
		assertSubstring("Semantic errors:\n" + 
				"\n" + 
				"*** Errors: 5\n" + 
				"\n" + 
				"line 13, col 1 to line 13, col 52 of module test213\n" + 
				"\n" + 
				"Level error in instantiating module 'test213b':\n" + 
				"The level of the expression or operator substituted for 'C' \n" + 
				"must be at most 2.\n" + 
				"\n" + 
				"\n" + 
				"line 14, col 1 to line 14, col 52 of module test213\n" + 
				"\n" + 
				"Level error in instantiating module 'test213b':\n" + 
				"The level of the expression or operator substituted for 'D' \n" + 
				"must be at most 2.\n" + 
				"\n" + 
				"\n" + 
				"line 29, col 8 to line 29, col 15 of module test213\n" + 
				"\n" + 
				"Non-constant CASE for temporal goal.\n" + 
				"\n" + 
				"\n" + 
				"line 31, col 8 to line 31, col 15 of module test213\n" + 
				"\n" + 
				"Non-constant TAKE, WITNESS, or HAVE for temporal goal.\n" + 
				"\n" + 
				"\n" + 
				"line 33, col 8 to line 33, col 22 of module test213\n" + 
				"\n" + 
				"Non-constant TAKE, WITNESS, or HAVE for temporal goal.\n" + 
				"\n" + 
				"\n" + 
				"");
	}
}
