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
package pcal;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.util.Arrays;

import org.junit.Test;

import util.ToolIO;

public class UnhandledInvalidSyntaxTest extends PCalTest {

	@Test
	public void test1() throws IOException {
		assertEquals(trans.STATUS_EXIT_WITH_ERRORS, trans.runMe(new String[] {"-nocfg", 
							writeTempFile("MissingSemicolonTest1", 
				"---- MODULE algo ----\n" + 
				"(*\n" + 
				" --algorithm algo\n" + 
				" begin\n" + 
				" await;\n" +
				" end algorithm;\n" +
				"*)\n" + 
				"===="
			)}));
		
		assertTrue(Arrays.toString(ToolIO.getAllMessages()),
				Arrays.asList(ToolIO.getAllMessages()).contains("\nUnrecoverable error:\n"
					+ " -- Unknown error at or before\n"
					+ "    line 5, column 2.\n"));
	}
	
	@Test
	public void test2() throws IOException {
		assertEquals(trans.STATUS_EXIT_WITH_ERRORS, trans.runMe(new String[] {"-nocfg", 
							writeTempFile("MissingSemicolonTest2", 
				"---- MODULE algo ----\n" + 
				"(*\n" + 
				" --algorithm algo\n" + 
				" begin\n" + 
				" if TRUE then\n" + // missing semicolon
				" end if;\n" +
				" end algorithm;\n" +
				"*)\n" + 
				"===="
			)}));
		
		assertTrue(Arrays.toString(ToolIO.getAllMessages()),
				Arrays.asList(ToolIO.getAllMessages()).contains("\nUnrecoverable error:\n"
					+ " -- Unknown error at or before\n"
					+ "    line 6, column 8.\n"));
	}
}