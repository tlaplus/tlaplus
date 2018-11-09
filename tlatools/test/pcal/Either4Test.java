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

public class Either4Test extends PCalModelCheckerTestCase {

	public Either4Test() {
		super("Either4", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "81"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "154", "81", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "7"));

		assertCoverage("  line 35, col 21 to line 35, col 47 of module Either4: 18\n" + 
				"  line 36, col 21 to line 36, col 51 of module Either4: 18\n" + 
				"  line 37, col 31 to line 37, col 38 of module Either4: 0\n" + 
				"  line 38, col 21 to line 38, col 47 of module Either4: 18\n" + 
				"  line 39, col 21 to line 39, col 51 of module Either4: 18\n" + 
				"  line 40, col 31 to line 40, col 38 of module Either4: 0\n" + 
				"  line 41, col 21 to line 41, col 49 of module Either4: 18\n" + 
				"  line 42, col 21 to line 42, col 51 of module Either4: 18\n" + 
				"  line 43, col 31 to line 43, col 38 of module Either4: 0\n" + 
				"  line 46, col 15 to line 46, col 51 of module Either4: 18\n" + 
				"  line 47, col 15 to line 47, col 45 of module Either4: 18\n" + 
				"  line 48, col 25 to line 48, col 34 of module Either4: 0\n" + 
				"  line 51, col 15 to line 51, col 51 of module Either4: 18\n" + 
				"  line 52, col 15 to line 52, col 45 of module Either4: 18\n" + 
				"  line 53, col 25 to line 53, col 34 of module Either4: 0\n" + 
				"  line 57, col 21 to line 57, col 57 of module Either4: 36\n" + 
				"  line 59, col 21 to line 59, col 57 of module Either4: 18\n" + 
				"  line 64, col 15 to line 64, col 48 of module Either4: 54\n" + 
				"  line 65, col 25 to line 65, col 34 of module Either4: 0\n" + 
				"  line 71, col 70 to line 71, col 73 of module Either4: 0");
	}
}
