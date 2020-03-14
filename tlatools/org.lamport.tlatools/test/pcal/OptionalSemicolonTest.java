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
package pcal;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import tla2sany.drivers.SANY;
import util.TestPrintStream;
import util.ToolIO;

public class OptionalSemicolonTest extends PCalTest {
	
	/*
	 * A PlusCal User's Manual P-Syntax:
	 * "[...] the final semicolon [or comma] is optional in the p-syntax."
	 */
	
	@Test
	public void noOptionalSemiColonVariableList1() throws IOException {
		// Translate from PCal to TLA+
		final String filename = "MissingSemiColonVariableListTest1" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" + 
				"(*\n" + 
				"--algorithm algo\n" + 
				"variables foo = 0" + // no optional semicolon
				"\n" + 
				"fair process bug = 0\n" + // notice the "fair" statement 
				"begin\n" + 
				"L:\n" + 
				"    skip\n" + 
				"end process\n" + 
				"\n" + 
				"end algorithm *)\n" + 
				"===="
				);
		test(filename, absolutePath);
	}
	
	@Test
	public void noOptionalSemiColonVariableList2() throws IOException {
		// Translate from PCal to TLA+
		final String filename = "MissingSemiColonVariableListTest2" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" + 
				"(*\n" + 
				"--algorithm algo\n" + 
				"variables foo = 0 ;" + // optional semicolon
				"\n" + 
				"fair process bug = 0\n" + // notice the "fair" statement 
				"begin\n" + 
				"L:\n" + 
				"    skip\n" + 
				"end process\n" + 
				"\n" + 
				"end algorithm *)\n" + 
				"===="
				);
		test(filename, absolutePath);
	}
	
	@Test
	public void noOptionalSemiColonVariableList3() throws IOException {
		// Translate from PCal to TLA+
		final String filename = "MissingSemiColonVariableListTest3" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" + 
				"(*\n" + 
				"--algorithm algo\n" + 
				"variables foo = 0 ;" + // optional semicolon
				"\n" + 
				"process bug = 0\n" + // notice the "fair" statement 
				"begin\n" + 
				"L:\n" + 
				"    skip\n" + 
				"end process\n" + 
				"\n" + 
				"end algorithm *)\n" + 
				"===="
				);
		test(filename, absolutePath);
	}
	
	@Test
	public void noOptionalSemiColonVariableList4() throws IOException {
		// Translate from PCal to TLA+
		final String filename = "MissingSemiColonVariableListTest4" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" + 
				"(*\n" + 
				"--algorithm algo\n" + 
				"variables foo = 0" + // no optional semicolon
				"\n" + 
				"process bug = 0\n" + // no "fair" statement 
				"begin\n" + 
				"L:\n" + 
				"    skip\n" + 
				"end process\n" + 
				"\n" + 
				"end algorithm *)\n" + 
				"===="
				);
		test(filename, absolutePath);
	}

	private void test(final String filename, final String absolutePath) {
		assertEquals(trans.STATUS_EXIT_WITHOUT_ERROR, trans.runMe(new String[] { "-nocfg", absolutePath }));

		// Parse with SANY and check for errors (collects parse errors into ToolIO.out)
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		SANY.SANYmain(new String[] { absolutePath });
		testPrintStream.assertSubstring("Semantic processing of module " + filename);
	}
}
