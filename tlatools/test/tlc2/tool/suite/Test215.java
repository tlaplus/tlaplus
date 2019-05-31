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

public class Test215 extends SuiteETestCase {

	public Test215() {
		super(ExitStatus.ERROR_SPEC_PARSE);
	}
	
	@Test
	public void testSpec() {
		assertFalse(recorder.recorded(EC.GENERAL));
		assertSubstring("Semantic errors:\n" + 
				"\n" + 
				"*** Errors: 8\n" + 
				"\n" + 
				"line 8, col 6 to line 8, col 14 of module test215\n" + 
				"\n" + 
				"Action used where only temporal formula or state predicate allowed.\n" + 
				"\n" + 
				"\n" + 
				"line 9, col 6 to line 9, col 14 of module test215\n" + 
				"\n" + 
				"Action used where only temporal formula or state predicate allowed.\n" + 
				"\n" + 
				"\n" + 
				"line 12, col 6 to line 12, col 16 of module test215\n" + 
				"\n" + 
				"Action used where only temporal formula or state predicate allowed.\n" + 
				"\n" + 
				"\n" + 
				"line 13, col 6 to line 13, col 16 of module test215\n" + 
				"\n" + 
				"Action used where only temporal formula or state predicate allowed.\n" + 
				"\n" + 
				"\n" + 
				"line 16, col 6 to line 16, col 11 of module test215\n" + 
				"\n" + 
				"<> followed by action not of form <<A>>_v.\n" + 
				"\n" + 
				"\n" + 
				"line 20, col 8 to line 20, col 13 of module test215\n" + 
				"\n" + 
				"[] followed by action not of form [A]_v.\n" + 
				"\n" + 
				"\n" + 
				"line 23, col 25 to line 23, col 26 of module test215\n" + 
				"\n" + 
				"Action-level bound of quantified temporal formula.\n" + 
				"\n" + 
				"\n" + 
				"line 26, col 26 to line 26, col 27 of module test215\n" + 
				"\n" + 
				"Action-level bound of quantified temporal formula.\n" + 
				"\n" + 
				"\n");
	}
}
