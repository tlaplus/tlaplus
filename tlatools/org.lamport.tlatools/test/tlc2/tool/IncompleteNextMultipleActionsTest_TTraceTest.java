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

package tlc2.tool;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Ignore;
import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.TTraceModelCheckerTestCase;

public class IncompleteNextMultipleActionsTest_TTraceTest extends TTraceModelCheckerTestCase {

	public IncompleteNextMultipleActionsTest_TTraceTest() {
		super(IncompleteNextMultipleActionsTest.class, ExitStatus.FAILURE_SPEC_EVAL);
	}

    @Ignore("https://github.com/tlaplus/tlaplus/pull/588#issuecomment-821745313")
	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2", "1", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(4);
		expectedTrace.add("/\\ x = 0\n/\\ y = 0\n/\\ z = 0");
		expectedTrace.add("/\\ x = 1\n/\\ y = null\n/\\ z = null");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
		
		// Assert TLC indicates unassigned variable
		assertTrue(recorder.recorded(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT));
		final List<Object> records = recorder.getRecords(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT);
		assertEquals("A1", ((String[]) records.get(0))[0]);
		assertEquals("s are", ((String[]) records.get(0))[1]);
		assertEquals("y, z", ((String[]) records.get(0))[2]);

		assertUncovered("line 8, col 16 to line 8, col 21 of module IncompleteNextMultipleActions: 0\n"
				+ "line 8, col 26 to line 8, col 31 of module IncompleteNextMultipleActions: 0\n"
				+ "line 8, col 7 to line 8, col 11 of module IncompleteNextMultipleActions: 0\n");
	}
}
