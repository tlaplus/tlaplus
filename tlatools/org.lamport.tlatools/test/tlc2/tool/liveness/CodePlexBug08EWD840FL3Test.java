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
import tlc2.output.EC.ExitStatus;

/**
 * see http://tlaplus.codeplex.com/workitem/8
 */
public class CodePlexBug08EWD840FL3Test extends ModelCheckerTestCase {

	public CodePlexBug08EWD840FL3Test() {
		super("EWD840MC3", "CodePlexBug08", ExitStatus.VIOLATION_LIVENESS);
	}
	
	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "15986", "1566", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		assertNodeAndPtrSizes(143808L, 25040L);
		
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>();
		expectedTrace.add("/\\ tpos = 0\n"
		                + "/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
		                + "/\\ tcolor = \"black\"\n"
		                + "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")");
		expectedTrace.add("/\\ tpos = 3\n"
		                + "/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
		                + "/\\ tcolor = \"white\"\n"
		                + "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")");
		expectedTrace.add("/\\ tpos = 3\n"
		                + "/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
		                + "/\\ tcolor = \"white\"\n"
		                + "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")");
		expectedTrace.add("/\\ tpos = 3\n"
		                + "/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE)\n"
		                + "/\\ tcolor = \"white\"\n"
		                + "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")");
		expectedTrace.add("/\\ tpos = 2\n"
		                + "/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE)\n"
		                + "/\\ tcolor = \"white\"\n"
		                + "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")");
		expectedTrace.add("/\\ tpos = 2\n"
		                + "/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
		                + "/\\ tcolor = \"white\"\n"
		                + "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"black\" @@ 3 :> \"white\")");
		expectedTrace.add("/\\ tpos = 1\n"
		                + "/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
		                + "/\\ tcolor = \"black\"\n"
		                + "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")");
		expectedTrace.add("/\\ tpos = 1\n"
		                + "/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
		                + "/\\ tcolor = \"black\"\n"
		                + "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
		
		// last state loops back to state 1
		assertBackToState(1);

	assertZeroUncovered();
	}
}
