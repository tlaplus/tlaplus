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
public class CodePlexBug08EWD840FL1Test_TTraceTest extends TTraceModelCheckerTestCase {

	public CodePlexBug08EWD840FL1Test_TTraceTest() {
		super(CodePlexBug08EWD840FL1Test.class, "CodePlexBug08", ExitStatus.VIOLATION_LIVENESS);
	}
	
	@Test
	public void testSpec() {
		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "17", "16", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		assertNodeAndPtrSizes(464L, 256L);
		
		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(10);
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 0\n"
				+ "/\\ tcolor = \"black\"");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedTrace.add("/\\ active = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"white\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedTrace.add("/\\ active = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedTrace.add("/\\ active = (0 :> TRUE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> TRUE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 3\n"
				+ "/\\ tcolor = \"white\"");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"black\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 2\n"
				+ "/\\ tcolor = \"white\"");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> FALSE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 1\n"
				+ "/\\ tcolor = \"black\"");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> TRUE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 1\n"
				+ "/\\ tcolor = \"black\"");
		expectedTrace.add("/\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)\n"
				+ "/\\ color = (0 :> \"white\" @@ 1 :> \"black\" @@ 2 :> \"white\" @@ 3 :> \"white\")\n"
				+ "/\\ tpos = 1\n"
				+ "/\\ tcolor = \"black\"");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

		assertBackToState(1);

		assertZeroUncovered();
	}
}
