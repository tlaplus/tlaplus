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
package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.FileNotFoundException;
import java.io.IOException;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.TTraceModelCheckerTestCase;

public class Github597Test_TTraceTest extends TTraceModelCheckerTestCase {

	public Github597Test_TTraceTest() {
		super(Github597Test.class, EC.ExitStatus.VIOLATION_LIVENESS);
	}
	
	protected boolean noRandomFPandSeed() {
		return false;
	}
	
	protected boolean doCoverage() {
		return false;
	}
	
	protected boolean doDump() {
		return false;
	}

	@Test
	public void testSpec() throws FileNotFoundException, IOException {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		// Every run of this test generates a different trace, but the TE spec should
		// replicate it anyway. For now, simply check that a trace has been generated
		// and the TE spec also produces a trace.
		assertFalse(recorder.recorded(EC.GENERAL));

		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		assertBackToState();
	}
}
