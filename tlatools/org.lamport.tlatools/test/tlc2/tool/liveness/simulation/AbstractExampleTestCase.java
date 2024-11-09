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

package tlc2.tool.liveness.simulation;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public abstract class AbstractExampleTestCase extends ModelCheckerTestCase {

	private final String name;

	public AbstractExampleTestCase(final String cfg) {
		// Checks the depth parameter too. Depth <= 100 will cause simluation to
		// go on forever.
		super(cfg, "simulation", new String[] { "-simulate", "-depth", "11" }, ExitStatus.VIOLATION_LIVENESS);
		this.name = cfg;
	}
	
	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_STATS_SIMU, "12"));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(10);
		expectedTrace.add("/\\ x = 0\n/\\ l = 1");
		expectedTrace.add("/\\ x = 1\n/\\ l = 2");
		expectedTrace.add("/\\ x = 2\n/\\ l = 3");
		expectedTrace.add("/\\ x = 3\n/\\ l = 4");
		expectedTrace.add("/\\ x = 4\n/\\ l = 5");
		expectedTrace.add("/\\ x = 5\n/\\ l = 6");
		expectedTrace.add("/\\ x = 6\n/\\ l = 7");
		expectedTrace.add("/\\ x = 7\n/\\ l = 8");
		expectedTrace.add("/\\ x = 8\n/\\ l = 9");
		expectedTrace.add("/\\ x = 9\n/\\ l = 10");
		final List<String> expectedActions = new ArrayList<>(expectedTrace.size());
		expectedActions.add("<Init line 6, col 9 to line 6, col 13 of module " + name + ">");
		for (int i = 1; i < expectedTrace.size(); i++) {
			expectedActions.add("<Next line 8, col 9 to line 8, col 27 of module " + name + ">");
		}
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);
		assertBackToState(1, "<Next line 8, col 9 to line 8, col 27 of module " + name + ">");
		
		// Assert POSTCONDITION.
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_FALSE));
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_EVALUATION_ERROR));		
	}
}
