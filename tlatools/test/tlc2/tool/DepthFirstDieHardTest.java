/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;
import org.junit.Test;
import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class DepthFirstDieHardTest extends ModelCheckerTestCase {

	public DepthFirstDieHardTest() {
		super("DieHard", "", new String[] {"-dfid", "7"});
	}

	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT1));
		final List<String> expectedTrace = new ArrayList<String>(7);
		expectedTrace.add("/\\ action = \"nondet\"\n/\\ smallBucket = 0\n/\\ bigBucket = 0\n/\\ water_to_pour = 0");
		expectedTrace.add("/\\ action = \"fill big\"\n/\\ smallBucket = 0\n/\\ bigBucket = 5\n/\\ water_to_pour = 0");
		expectedTrace.add("/\\ action = \"pour big to small\"\n/\\ smallBucket = 3\n/\\ bigBucket = 2\n/\\ water_to_pour = 3");
		expectedTrace.add("/\\ action = \"empty small\"\n/\\ smallBucket = 0\n/\\ bigBucket = 2\n/\\ water_to_pour = 3");
		expectedTrace.add("/\\ action = \"pour big to small\"\n/\\ smallBucket = 2\n/\\ bigBucket = 0\n/\\ water_to_pour = 2");
		
		expectedTrace.add("/\\ action = \"fill big\"\n/\\ smallBucket = 2\n/\\ bigBucket = 5\n/\\ water_to_pour = 2");
		
		expectedTrace.add("/\\ action = \"pour big to small\"\n/\\ smallBucket = 3\n/\\ bigBucket = 4\n/\\ water_to_pour = 1");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT1), expectedTrace);
		assertCoverage("  line 58, col 19 to line 58, col 36 of module DieHard: 53\n" +
				"  line 59, col 19 to line 59, col 32 of module DieHard: 53\n" +
				"  line 60, col 29 to line 60, col 58 of module DieHard: 0\n" +
				"  line 61, col 19 to line 61, col 37 of module DieHard: 53\n" +
				"  line 62, col 19 to line 62, col 32 of module DieHard: 53\n" +
				"  line 63, col 29 to line 63, col 58 of module DieHard: 0\n" +
				"  line 64, col 19 to line 64, col 38 of module DieHard: 53\n" +
				"  line 65, col 19 to line 65, col 34 of module DieHard: 53\n" +
				"  line 66, col 29 to line 66, col 56 of module DieHard: 0\n" +
				"  line 67, col 19 to line 67, col 39 of module DieHard: 53\n" +
				"  line 68, col 19 to line 68, col 34 of module DieHard: 53\n" +
				"  line 69, col 29 to line 69, col 56 of module DieHard: 0\n" +
				"  line 70, col 19 to line 70, col 40 of module DieHard: 53\n" +
				"  line 71, col 19 to line 71, col 66 of module DieHard: 53\n" +
				"  line 72, col 19 to line 72, col 61 of module DieHard: 53\n" +
				"  line 73, col 19 to line 73, col 57 of module DieHard: 53\n" +
				"  line 74, col 19 to line 74, col 40 of module DieHard: 52\n" +
				"  line 75, col 19 to line 75, col 66 of module DieHard: 52\n" +
				"  line 76, col 19 to line 76, col 61 of module DieHard: 52\n" +
				"  line 77, col 19 to line 77, col 57 of module DieHard: 52");
	}
}
