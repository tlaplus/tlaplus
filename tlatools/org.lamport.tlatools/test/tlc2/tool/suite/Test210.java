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

public class Test210 extends SuiteETestCase {
	
	public Test210() {
		super(ExitStatus.ERROR_SPEC_PARSE);
	}
	
	@Test
	public void testSpec() {
		assertFalse(recorder.recorded(EC.GENERAL));
		assertSubstring("Semantic errors:\n" + 
				"\n" + 
				"*** Errors: 9\n" + 
				"\n" + 
				"line 33, col 16 to line 33, col 19 of module test210\n" + 
				"\n" + 
				"Accessing subexpression labeled `laby' of ASSUME/PROVE clause within the scope of a declaration\n" + 
				" from outside that declaration's scope.\n" + 
				"\n" + 
				"\n" + 
				"line 35, col 16 to line 35, col 16 of module test210\n" + 
				"\n" + 
				"Accessing ASSUME/PROVE clause within the scope of a declaration\n" + 
				" from outside that declaration's scope.\n" + 
				"\n" + 
				"\n" + 
				"line 42, col 41 to line 42, col 55 of module test210\n" + 
				"\n" + 
				"Label not allowed within scope of declaration in nested ASSUME/PROVE.\n" + 
				"\n" + 
				"\n" + 
				"line 43, col 30 to line 43, col 44 of module test210\n" + 
				"\n" + 
				"Label not allowed within scope of declaration in nested ASSUME/PROVE.\n" + 
				"\n" + 
				"\n" + 
				"line 55, col 16 to line 55, col 16 of module test210\n" + 
				"\n" + 
				"Accessing non-existent subexpression of a SUFFICES\n" + 
				"\n" + 
				"\n" + 
				"line 62, col 15 to line 62, col 18 of module test210\n" + 
				"\n" + 
				"Accessing subexpression labeled `laby' of ASSUME/PROVE clause within the scope of a declaration\n" + 
				" from outside that declaration's scope.\n" + 
				"\n" + 
				"\n" + 
				"line 63, col 15 to line 63, col 18 of module test210\n" + 
				"\n" + 
				"Accessing subexpression labeled `labi' of ASSUME/PROVE clause within the scope of a declaration\n" + 
				" from outside that declaration's scope.\n" + 
				"\n" + 
				"\n" + 
				"line 64, col 15 to line 64, col 18 of module test210\n" + 
				"\n" + 
				"Accessing subexpression labeled `labu' of ASSUME/PROVE clause within the scope of a declaration\n" + 
				" from outside that declaration's scope.\n" + 
				"\n" + 
				"\n" + 
				"line 65, col 15 to line 65, col 15 of module test210\n" + 
				"\n" + 
				"Accessing ASSUME/PROVE clause within the scope of a declaration\n" + 
				" from outside that declaration's scope.\n" + 
				"\n" + 
				"\n");
	}
}
