/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved. 
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
package tla2sany;

import java.io.File;

import org.junit.Test;

import tla2sany.drivers.SANY;
import tlc2.tool.CommonTestCase;
import util.TestPrintStream;
import util.ToolIO;

public class RecursiveDefDeclMismatchTest extends SANYTest {

	@Test
	public void test() {
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		ToolIO.err = testPrintStream;
		
		SANY.SANYmain(new String[] { CommonTestCase.BASE_PATH + File.separator + "sany" + File.separator + "RecursiveDefDeclMismatch.tla" });

		testPrintStream.assertSubstring("Definition of CountDown has different arity than its RECURSIVE declaration.");
		testPrintStream.assertSubstring("The operator CountDown requires 2 arguments.");
	}
}
