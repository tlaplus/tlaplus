/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved. 
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
package tla2sany.drivers;

import org.junit.Test;

import tlc2.tool.CommonTestCase;
import util.TestPrintStream;
import util.ToolIO;

public class IllegalOperatorTest  {

	@Test
	public void test() {
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		
		SANY.SANYmain(
				new String[] { CommonTestCase.BASE_PATH + "IllegalOperatorTest" });
		
		testPrintStream.assertSubstring("*** Errors: 1\n" + 
				"\n" + 
				"line 3, col 8 to line 3, col 11 of module IllegalOperatorTest\n" + 
				"\n" + 
				"Argument number 1 to operator 'D' \n" + 
				"should be a 1-parameter operator.");
	}
}
