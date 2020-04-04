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

import org.junit.Ignore;
import org.junit.Test;

import tlc2.output.EC;

public class SymmetryModelCheckerTestLonga extends ModelCheckerTestCase {

	public SymmetryModelCheckerTestLonga() {
		super("LongMCa", "symmetry");
	}
	
	@Test
	@Ignore("Ignored for as long as symmetry is incorrectly handled by TLC with liveness checking.")
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "7", "5", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));

		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		assertNodeAndPtrSizes(180L, 80L);

		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(4);
		expectedTrace.add("/\\ x = a\n/\\ y = 0");
		expectedTrace.add("/\\ x = a\n/\\ y = 1");
		expectedTrace.add("/\\ x = a\n/\\ y = 2");
		expectedTrace.add("/\\ x = a\n/\\ y = 3");
		expectedTrace.add("/\\ x = a\n/\\ y = 4"); // <= x changes after this state
		expectedTrace.add("/\\ x = b\n/\\ y = 0");
		expectedTrace.add("/\\ x = b\n/\\ y = 1");
		expectedTrace.add("/\\ x = b\n/\\ y = 2");
		expectedTrace.add("/\\ x = b\n/\\ y = 3");
		expectedTrace.add("/\\ x = b\n/\\ y = 4");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
		
		assertBackToState(1, "<Action line 25, col 12 to line 27, col 27 of module SymmetryLivenessLong>");
	}
}
