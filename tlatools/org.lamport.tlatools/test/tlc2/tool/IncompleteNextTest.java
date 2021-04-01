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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class IncompleteNextTest extends ModelCheckerTestCase {

	public IncompleteNextTest() {
		super("IncompleteNext", ExitStatus.FAILURE_SPEC_EVAL);
	}

	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2", "1", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(2);
		final List<String> expectedActions = new ArrayList<String>(2);
		expectedTrace.add("/\\ x = 0\n/\\ y = 0");
		expectedActions.add(isExtendedTLCState()
				? "<Initial predicate line 6, col 19 to line 6, col 21 of module IncompleteNext>"
				: TLCStateInfo.INITIAL_PREDICATE);
		expectedTrace.add("/\\ x = 1\n/\\ y = null");
		expectedActions.add("<Action line 6, col 30 to line 6, col 35 of module IncompleteNext>");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace, expectedActions);
		
		// Assert TLC indicates unassigned variable
		assertTrue(recorder.recorded(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT));
		final List<Object> records = recorder.getRecords(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT);
		assertEquals(" is", ((String[]) records.get(0))[0]);
		assertEquals("y", ((String[]) records.get(0))[1]);

		assertZeroUncovered();
	}
}
