/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved. 
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

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class EmptySubsetEqTest extends ModelCheckerTestCase {

	// This the supplements SubsetEqTest. It checks that TLC does not
	// incorrectly reduce the expression SUBSET (1..3) \subseteq (1..4). The
	// empty subset {} is not a subset of (1..4).
	public EmptySubsetEqTest() {
		super("EmptySubsetEq", ExitStatus.FAILURE_SPEC_EVAL);
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "1", "1", "0"));

		assertNoTESpec();

		assertTrue(recorder.recordedWithStringValue(EC.GENERAL,
				"TLC threw an unexpected exception.\nThis was probably caused by an "
				+ "error in the spec or model.\nSee the User Output or TLC Console "
				+ "for clues to what happened.\nThe exception was a "
				+ "java.lang.RuntimeException\n: Attempted to check if the value:\n"
				+ "{}\nis in the integer interval 1..4"));

		// Expect an error trace consisting of a single state.
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(4);
		expectedTrace.add("b = TRUE");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

		assertUncovered("line 8, col 9 to line 8, col 48 of module EmptySubsetEq: 0\n");
	}
}
