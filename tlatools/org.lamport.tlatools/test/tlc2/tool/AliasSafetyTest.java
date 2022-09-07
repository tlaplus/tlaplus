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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.ArrayList;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.BlockJUnit4ClassRunner;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.value.IValue;
import tlc2.value.impl.IntValue;

@RunWith(BlockJUnit4ClassRunner.class)
public class AliasSafetyTest extends ModelCheckerTestCase {

	public AliasSafetyTest() {
		super("Alias", new String[] { "-config", "Alias.tla" }, EC.ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "4", "4", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "4"));

		assertFalse(recorder.recorded(EC.GENERAL));

		// Assert the error trace
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(7);
		// Trace prefix
		expectedTrace.add("/\\ y = FALSE\n/\\ x = 1\n/\\ a = 1\n/\\ b = FALSE\n/\\ anim = \"e1: 1 e2: FALSE\"\n/\\ te = TRUE\n/\\ lvl = <<1, 1>>\n/\\ trc = <<[x |-> 1, y |-> FALSE]>>");
		expectedTrace.add("/\\ y = TRUE\n/\\ x = 2\n/\\ a = 1\n/\\ b = FALSE\n/\\ anim = \"e1: 2 e2: TRUE\"\n/\\ te = TRUE\n/\\ lvl = <<2, 2>>\n/\\ trc = <<[x |-> 1, y |-> FALSE], [x |-> 2, y |-> TRUE]>>");
		expectedTrace.add("/\\ y = FALSE\n/\\ x = 3\n/\\ a = 1\n/\\ b = FALSE\n/\\ anim = \"e1: 3 e2: FALSE\"\n/\\ te = TRUE\n/\\ lvl = <<3, 3>>\n/\\ trc = <<[x |-> 1, y |-> FALSE], [x |-> 2, y |-> TRUE], [x |-> 3, y |-> FALSE]>>");
		expectedTrace.add("/\\ y = TRUE\n/\\ x = 4\n/\\ a = 0\n/\\ b = TRUE\n/\\ anim = \"e1: 4 e2: TRUE\"\n/\\ te = TRUE\n/\\ lvl = <<4, 4>>\n/\\ trc = << [x |-> 1, y |-> FALSE],\n"
				+ "   [x |-> 2, y |-> TRUE],\n"
				+ "   [x |-> 3, y |-> FALSE],\n"
				+ "   [x |-> 4, y |-> TRUE] >>");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
		
		// Assert POSTCONDITION.
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_FALSE));
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_EVALUATION_ERROR));

		// Check that POSTCONDITION wrote the number of generated states to a TLCSet
		// register.
		final List<IValue> allValue = TLCGlobals.mainChecker.getAllValue(42);
		assertTrue(!allValue.isEmpty());
		assertEquals(IntValue.gen(4), allValue.get(0));
	}
}
