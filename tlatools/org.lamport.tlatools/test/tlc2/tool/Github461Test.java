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

import static org.junit.Assert.assertTrue;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github461Test extends ModelCheckerTestCase {

	public Github461Test() {
		super("Github461", EC.ExitStatus.VIOLATION_ASSERT);
	}

	@Test
	public void testSpec() throws FileNotFoundException, IOException {
		// Assert evaluation error.
		assertTrue(recorder.recordedWithStringValue(EC.TLC_VALUE_ASSERT_FAILED,
				"\"Failure of assertion at line 8, column 4.\""));

		// Assert an error trace.
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		
		// Assert the correct trace.
		final List<String> expectedTrace = new ArrayList<String>(4);
		expectedTrace.add("x = 0");
		expectedTrace.add("x = 1");
		expectedTrace.add("x = 2");
		expectedTrace.add("x = 3");
		expectedTrace.add("x = 4");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

		// Assert the underlying error message with stack trace.
		assertTrue(recorder.recordedWithStringValues(EC.TLC_NESTED_EXPRESSION,
				"0. Line 9, column 5 to line 10, column 17 in Github461\n" + 
				"1. Line 9, column 8 to line 9, column 65 in Github461\n" + 
				"\n"));
		
		assertZeroUncovered();
	}
}
