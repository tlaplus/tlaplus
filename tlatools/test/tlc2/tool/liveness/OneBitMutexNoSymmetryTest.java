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

import java.io.File;
import java.util.ArrayList;
import java.util.List;
import org.junit.Test;
import tlc2.output.EC;

public class OneBitMutexNoSymmetryTest extends ModelCheckerTestCase {

	public OneBitMutexNoSymmetryTest() {
		super("OneBitMutexNoSymmetryMC", "symmetry" + File.separator + "OneBitMutex");
	}
	
	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "244", "127", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));

		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		
		assertNodeAndPtrSizes(11700L, 3728L);

		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(17);
		//1
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> FALSE)\n" 
						+ "/\\ pc = (A :> \"ncs\" @@ B :> \"ncs\")");
		//2
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n"
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> FALSE)\n"
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"ncs\")");
		//3
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n"
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> FALSE)\n"
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e1\")");
		//4
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {A})\n"
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e2\")");
		//5
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e3\")");
		//6
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e2\")");
		//7
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"cs\")");
		//8 (Loops back to)
		expectedTrace.add("/\\ unchecked = (A :> {B} @@ B :> {})\n" 
						+ "/\\ other = (A :> A @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e2\" @@ B :> \"cs\")");
		//9
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e3\" @@ B :> \"cs\")");
		//10
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e3\" @@ B :> \"f\")");
		//11
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e4\" @@ B :> \"f\")");
		//12
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> FALSE)\n" 
						+ "/\\ pc = (A :> \"e4\" @@ B :> \"ncs\")");
		//13
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> FALSE)\n" 
						+ "/\\ pc = (A :> \"e4\" @@ B :> \"e1\")");
		//14
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> FALSE)\n" 
						+ "/\\ pc = (A :> \"e5\" @@ B :> \"e1\")");
		//15
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> FALSE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e1\")");
		//16
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {A})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e2\")");
		//17
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e3\")");
		//18
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> FALSE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e1\" @@ B :> \"e2\")");
		//19
		expectedTrace.add("/\\ unchecked = (A :> {B} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e2\" @@ B :> \"e2\")");
		//20
		expectedTrace.add("/\\ unchecked = (A :> {} @@ B :> {})\n" 
						+ "/\\ other = (A :> B @@ B :> A)\n"
						+ "/\\ x = (A :> TRUE @@ B :> TRUE)\n" 
						+ "/\\ pc = (A :> \"e3\" @@ B :> \"e2\")");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

		assertBackToState(9, "<e2 line 66, col 13 to line 74, col 21 of module OneBitMutex>");

	assertCoverage("  line 101, col 16 to line 101, col 46 of module OneBitMutex: 18\n" +
		"  line 102, col 26 to line 102, col 50 of module OneBitMutex: 0\n" +
		"  line 105, col 15 to line 105, col 45 of module OneBitMutex: 18\n" +
		"  line 106, col 15 to line 106, col 47 of module OneBitMutex: 18\n" +
		"  line 107, col 25 to line 107, col 46 of module OneBitMutex: 0\n" +
		"  line 57, col 17 to line 57, col 48 of module OneBitMutex: 44\n" +
		"  line 58, col 27 to line 58, col 51 of module OneBitMutex: 0\n" +
		"  line 61, col 16 to line 61, col 45 of module OneBitMutex: 44\n" +
		"  line 62, col 16 to line 62, col 71 of module OneBitMutex: 44\n" +
		"  line 63, col 16 to line 63, col 47 of module OneBitMutex: 44\n" +
		"  line 64, col 16 to line 64, col 29 of module OneBitMutex: 44\n" +
		"  line 69, col 29 to line 69, col 63 of module OneBitMutex: 48\n" +
		"  line 70, col 27 to line 70, col 100 of module OneBitMutex: 48\n" +
		"  line 71, col 27 to line 71, col 58 of module OneBitMutex: 48\n" +
		"  line 72, col 27 to line 72, col 58 of module OneBitMutex: 18\n" +
		"  line 73, col 37 to line 73, col 58 of module OneBitMutex: 0\n" +
		"  line 74, col 16 to line 74, col 21 of module OneBitMutex: 66\n" +
		"  line 79, col 38 to line 79, col 69 of module OneBitMutex: 14\n" +
		"  line 80, col 38 to line 80, col 69 of module OneBitMutex: 0\n" +
		"  line 81, col 27 to line 81, col 58 of module OneBitMutex: 10\n" +
		"  line 82, col 26 to line 82, col 50 of module OneBitMutex: 0\n" +
		"  line 85, col 16 to line 85, col 46 of module OneBitMutex: 20\n" +
		"  line 86, col 16 to line 86, col 47 of module OneBitMutex: 20\n" +
		"  line 87, col 26 to line 87, col 47 of module OneBitMutex: 0\n" +
		"  line 91, col 16 to line 91, col 47 of module OneBitMutex: 6\n" +
		"  line 92, col 26 to line 92, col 50 of module OneBitMutex: 0\n" +
		"  line 96, col 16 to line 96, col 47 of module OneBitMutex: 0\n" +
		"  line 97, col 26 to line 97, col 50 of module OneBitMutex: 0");
	}
}
