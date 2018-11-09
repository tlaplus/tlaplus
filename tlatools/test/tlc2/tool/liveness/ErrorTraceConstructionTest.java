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

package tlc2.tool.liveness;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;
import org.junit.Test;
import tlc2.output.EC;

public class ErrorTraceConstructionTest extends ModelCheckerTestCase {

	public ErrorTraceConstructionTest() {
		super("ErrorTraceConstructionMC", "symmetry");
	}
	
	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "9", "8", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		assertNodeAndPtrSizes(288L, 128L);
	
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(4);
		expectedTrace.add("/\\ x = 0\n/\\ y = 0");
		expectedTrace.add("/\\ x = 0\n/\\ y = 1");
		expectedTrace.add("/\\ x = 0\n/\\ y = 2");
		expectedTrace.add("/\\ x = 0\n/\\ y = 3");
		expectedTrace.add("/\\ x = 0\n/\\ y = 4");
		expectedTrace.add("/\\ x = 1\n/\\ y = 5");
		expectedTrace.add("/\\ x = 0\n/\\ y = 6");
		expectedTrace.add("/\\ x = 0\n/\\ y = 7");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
		
		assertBackToState(4, "<N7 line 32, col 7 to line 34, col 19 of module ErrorTraceConstruction>");

	assertCoverage("  line 12, col 14 to line 12, col 21 of module ErrorTraceConstruction: 1\n" +
		"  line 13, col 14 to line 13, col 19 of module ErrorTraceConstruction: 1\n" +
		"  line 15, col 14 to line 15, col 21 of module ErrorTraceConstruction: 1\n" +
		"  line 16, col 14 to line 16, col 19 of module ErrorTraceConstruction: 1\n" +
		"  line 18, col 14 to line 18, col 21 of module ErrorTraceConstruction: 1\n" +
		"  line 19, col 14 to line 19, col 19 of module ErrorTraceConstruction: 1\n" +
		"  line 21, col 14 to line 21, col 21 of module ErrorTraceConstruction: 1\n" +
		"  line 22, col 14 to line 22, col 19 of module ErrorTraceConstruction: 1\n" +
		"  line 24, col 14 to line 24, col 21 of module ErrorTraceConstruction: 1\n" +
		"  line 25, col 14 to line 25, col 26 of module ErrorTraceConstruction: 1\n" +
		"  line 27, col 14 to line 27, col 21 of module ErrorTraceConstruction: 1\n" +
		"  line 28, col 14 to line 28, col 26 of module ErrorTraceConstruction: 1\n" +
		"  line 30, col 14 to line 30, col 21 of module ErrorTraceConstruction: 1\n" +
		"  line 31, col 14 to line 31, col 19 of module ErrorTraceConstruction: 1\n" +
		"  line 33, col 14 to line 33, col 19 of module ErrorTraceConstruction: 1\n" +
		"  line 34, col 14 to line 34, col 19 of module ErrorTraceConstruction: 1");
	}
}
