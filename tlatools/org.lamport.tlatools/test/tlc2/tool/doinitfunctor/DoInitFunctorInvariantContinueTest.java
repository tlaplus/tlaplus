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

package tlc2.tool.doinitfunctor;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class DoInitFunctorInvariantContinueTest extends ModelCheckerTestCase {
	
	public DoInitFunctorInvariantContinueTest() {
		super("DoInitFunctorInvariantContinue", "DoInitFunctor", new String[] {"-continue"}/*, ExitStatus.VIOLATION_SAFETY*/);  //TODO The exit status is incorrect because TLC shows "no error" regardless of the number of violations with "-continue"
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "21", "11"));
		assertFalse(recorder.recorded(EC.GENERAL));

		assertTrue(recorder.recordedWithStringValues(EC.TLC_INVARIANT_VIOLATED_INITIAL, "Inv", "x = 1\n"));
		// Test that TLC - with continuation enabled - continues after finding the first inv violation.
		final List<Object> records = recorder.getRecords(EC.TLC_INVARIANT_VIOLATED_INITIAL);
		assertEquals(10, records.size());
		for (int j = 0; j < records.size(); j++) {
			final String[] violation = (String[]) records.get(j);
			assertEquals("Inv", violation[0]);
			assertEquals("x = " + (j+1) + "\n", violation[1]);
		}

		assertZeroUncovered();
	}
}
