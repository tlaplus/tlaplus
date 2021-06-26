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

public class Github317aTest extends ModelCheckerTestCase {

	public Github317aTest() {
		super("Github317a", new String[] { "-config", "Github317a.tla"}, EC.ExitStatus.ERROR);
	}

	@Override
	protected int getNumberOfThreads() {
		// Have multiple workers compete to report/print the error stack. Implies that
		// the actual error trace is non-deteministic and not asserted below.
		return Runtime.getRuntime().availableProcessors();
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));

		// Assert there is a trace.
		assertFalse(recorder.getRecords(EC.TLC_STATE_PRINT2).isEmpty());

		// Assert the right error trace has been printed.
		assertTrue(recorder.recordedWithStringValues(EC.TLC_NESTED_EXPRESSION,
				"0. Line 138, column 41 to line 138, column 48 in Github317a\n"
				+ "1. Line 117, column 13 to line 133, column 54 in Github317a\n"
				+ "2. Line 118, column 15 to line 133, column 54 in Github317a\n"
				+ "3. Line 128, column 23 to line 133, column 54 in Github317a\n"
				+ "4. Line 128, column 26 to line 128, column 67 in Github317a\n"
				+ "5. Line 129, column 26 to line 132, column 50 in Github317a\n"
				+ "6. Line 129, column 29 to line 129, column 59 in Github317a\n"
				+ "7. Line 129, column 29 to line 129, column 42 in Github317a\n\n"));
		
		// Assert error stack has only been printed once by one of the workers.
		assertEquals(1, recorder.getRecords(EC.TLC_NESTED_EXPRESSION).size());
	}
}
