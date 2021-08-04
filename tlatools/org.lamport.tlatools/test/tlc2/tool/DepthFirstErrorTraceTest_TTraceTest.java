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
import java.util.Collections;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.TTraceModelCheckerTestCase;

public class DepthFirstErrorTraceTest_TTraceTest extends TTraceModelCheckerTestCase {

	public DepthFirstErrorTraceTest_TTraceTest() {
		super(DepthFirstErrorTraceTest.class, ExitStatus.VIOLATION_SAFETY);
	}
	
	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
	
		// Assert the error trace
		assertFalse(recorder.recorded(EC.TLC_STATE_PRINT1));
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(5);
		expectedTrace.add("x = 0");
		expectedTrace.add("x = 1");
		expectedTrace.add("x = 2");
		expectedTrace.add("x = 3");
		expectedTrace.add("x = 4");
		expectedTrace.add("x = 5");
		expectedTrace.add("x = 6");
		expectedTrace.add("x = 7");		
        
        final List<String> expectedActions = new ArrayList<>();
        expectedActions.add("<_init line 23, col 5 to line 23, col 24 of module " + getModuleName() + ">");
        expectedActions.addAll(Collections.nCopies(expectedTrace.size() - 1, 
				"<_next line 27, col 5 to line 31, col 29 of module " + getModuleName() + ">"));
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);
		assertZeroUncovered();
	}
}
