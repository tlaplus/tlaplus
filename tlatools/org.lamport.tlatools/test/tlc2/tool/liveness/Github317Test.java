/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved.
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;

public class Github317Test extends ModelCheckerTestCase {

	public Github317Test() {
		super("Github317", new String[] { "-config", "Github317.tla"}, EC.ExitStatus.ERROR);
	}

	@Override
	protected int getNumberOfThreads() {
		// Have multiple workers compete to report/print the error stack. Implies that
		// the actual error trace is non-deterministic and not asserted below.
		return Runtime.getRuntime().availableProcessors();
	}

	@Override
	protected boolean noGenerateSpec() {
		// Because of getNumberOfThreads above, TLC runs with multiple workers. This leads
		// to non-determinism in the length of the error-trace (usually one state, but
		// occasionally two). Iff the length is greater than one, TLC would write a
		// trace spec, which causes this test to fail because it expects no trace spec to
		// be written. Thus, we generally turn off trace specs for any length.
		return true;
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));

		assertNoTESpec();

		// Assert there is a trace.
		assertFalse(recorder.getRecords(EC.TLC_STATE_PRINT2).isEmpty());

		assertTrue(recorder.recordedWithStringValues(EC.TLC_NESTED_EXPRESSION,
				"0. Line 18, column 20 to line 18, column 23 in Github317\n"
				+ "1. Line 10, column 9 to line 11, column 23 in Github317\n"
				+ "2. Line 10, column 12 to line 10, column 21 in Github317\n"
				+ "3. Line 11, column 12 to line 11, column 23 in Github317\n"
				+ "4. Line 18, column 15 to line 18, column 18 in Github317\n"
				+ "5. Line 5, column 9 to line 5, column 15 in Github317\n"
				+ "6. Line 5, column 13 to line 5, column 13 in Github317\n\n"));

		// Assert error stack has only been printed once by one of the workers.
		assertEquals(1, recorder.getRecords(EC.TLC_NESTED_EXPRESSION).size());

		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_LIVE,
				"b", "line 5, col 13 to line 5, col 13 of module Github317"));
	}
}
