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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class ContinueTest extends ModelCheckerTestCase {

	public ContinueTest() {
		super("Continue", new String[] { "-continue" }, ExitStatus.SUCCESS);
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}

	@Test
	public void testSpec() throws FileNotFoundException, IOException {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "32", "29", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "29"));

		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));

		assertNoTESpec();
		
		// With -continue, TLC simply prints two or more consecutive traces in no given
		// order (determined by concurrent BFS) to stdout. This means that the
		// MPRecorder just concatenates the traces and it is difficult to check them.
		// For now we check that the concatenated trace has the expected number of states.
		assertEquals(32, recorder.getRecords(EC.TLC_STATE_PRINT2).size());
//		// Trace 1
//		final List<String> expectedTrace = new ArrayList<String>(2);
//		expectedTrace.add("/\\ x = 1\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 2\n/\\ y = 2");
//		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
//		// Trace 2
//		final List<String> expectedTrace = new ArrayList<String>(30);
//		expectedTrace.add("/\\ x = 1\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 2\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 3\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 4\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 5\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 6\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 7\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 8\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 9\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 10\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 11\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 12\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 13\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 14\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 15\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 16\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 17\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 18\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 19\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 20\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 21\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 22\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 23\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 24\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 25\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 26\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 27\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 28\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 29\n/\\ y = 1");
//		expectedTrace.add("/\\ x = 30\n/\\ y = 1");
//		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

		assertZeroUncovered();
	}

	@Override
	protected int getNumberOfThreads() {
		return 3;
	}
}
