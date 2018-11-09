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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;

public class MPNoParamsTest extends PCalModelCheckerTestCase {

	public MPNoParamsTest() {
		super("MPNoParams", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "96"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "250", "96", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "13"));

	assertCoverage("  line 40, col 16 to line 40, col 29 of module MPNoParams: 108\n" +
		"  line 41, col 16 to line 41, col 63 of module MPNoParams: 108\n" +
		"  line 42, col 16 to line 42, col 66 of module MPNoParams: 108\n" +
		"  line 47, col 10 to line 49, col 52 of module MPNoParams: 27\n" +
		"  line 50, col 10 to line 50, col 38 of module MPNoParams: 27\n" +
		"  line 51, col 10 to line 51, col 19 of module MPNoParams: 27\n" +
		"  line 55, col 10 to line 55, col 40 of module MPNoParams: 8\n" +
		"  line 56, col 20 to line 56, col 35 of module MPNoParams: 0\n" +
		"  line 61, col 16 to line 63, col 64 of module MPNoParams: 81\n" +
		"  line 64, col 16 to line 64, col 47 of module MPNoParams: 81\n" +
		"  line 65, col 16 to line 65, col 25 of module MPNoParams: 81\n" +
		"  line 69, col 16 to line 69, col 49 of module MPNoParams: 24\n" +
		"  line 70, col 26 to line 70, col 41 of module MPNoParams: 0\n" +
		"  line 78, col 70 to line 78, col 73 of module MPNoParams: 0");
	}
}
