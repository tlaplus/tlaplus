/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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

public class RandomElementSimulationTest_TTraceTest extends TTraceModelCheckerTestCase {

	public RandomElementSimulationTest_TTraceTest() {
		super(RandomElementSimulationTest.class, ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void test() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.TLC_BUG));

		assertTrue(recorder.recorded(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT));
		
		final List<String> expectedTrace = new ArrayList<String>(11);
		expectedTrace.add("/\\ x = 843\n/\\ y = 0");
		expectedTrace.add("/\\ x = 843\n/\\ y = 1");
		expectedTrace.add("/\\ x = 227\n/\\ y = 2");
		expectedTrace.add("/\\ x = 227\n/\\ y = 3");
		expectedTrace.add("/\\ x = 502\n/\\ y = 4");
		expectedTrace.add("/\\ x = 535\n/\\ y = 5");
		expectedTrace.add("/\\ x = 277\n/\\ y = 6");
		expectedTrace.add("/\\ x = 327\n/\\ y = 7");
		expectedTrace.add("/\\ x = 729\n/\\ y = 8");
		expectedTrace.add("/\\ x = 550\n/\\ y = 9");
		expectedTrace.add("/\\ x = 318\n/\\ y = 10");
		List<Object> actualTrace = recorder.getRecords(EC.TLC_STATE_PRINT2);
		final List<String> expectedActions = new ArrayList<>();
		expectedActions.add("<_init line 25, col 5 to line 26, col 24 of module "+getModuleName()+">");
		expectedActions.addAll(Collections.nCopies(expectedTrace.size() - 1,
				"<_next line 30, col 5 to line 36, col 29 of module "+getModuleName()+">"));
		assertTraceWith(actualTrace, expectedTrace, expectedActions);

		assertZeroUncovered();
	}
}
