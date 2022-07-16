/*******************************************************************************
 * Copyright (c) 2022 Microsoft Research. All rights reserved. 
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

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github743Test extends ModelCheckerTestCase {

	public Github743Test() {
		super("Github743", EC.ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void testSpec() throws FileNotFoundException, IOException {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));

		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		
		// Assert the correct trace.
		final List<String> expectedTrace = new ArrayList<String>(4);
		expectedTrace.add("/\\ x = \"foo\"\n"
				+ "/\\ y = 0");
		expectedTrace.add("/\\ x = \"foo\"\n"
				+ "/\\ y = 1");
		expectedTrace.add("/\\ x = TRUE\n"
				+ "/\\ y = 3");
		expectedTrace.add("/\\ x = TRUE\n"
				+ "/\\ y = 5");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
	}
}
