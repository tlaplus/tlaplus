/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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

import java.util.List;
import java.util.Map;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.TTraceModelCheckerTestCase;
import tlc2.value.IBoolValue;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import util.UniqueString;

public class RandomSubsetTest_TTraceTest extends TTraceModelCheckerTestCase {

	public RandomSubsetTest_TTraceTest() {
		super(RandomSubsetTest.class, ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2", "2", "0"));
		assertEquals(2, recorder.getRecordAsInt(EC.TLC_SEARCH_DEPTH));

		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		
		final List<Object> actual = recorder.getRecords(EC.TLC_STATE_PRINT2);
		assertEquals(2, actual.size());
		
		final TLCStateInfo first = (TLCStateInfo) ((Object[]) actual.get(0))[0];
		if (isExtendedTLCState()) {
			assertEquals("<_init line 27, col 5 to line 29, col 24 of module "+getModuleName()+">", first.info);
		} else {
			assertTrue(((String) first.info).startsWith("<Initial predicate>"));
		}
		final Map<UniqueString, IValue> firstState = first.state.getVals();
		assertEquals(3, firstState.size());
		
		// Check x and y values are within defined ranges.
		final IntValue firstX = (IntValue) firstState.get(UniqueString.uniqueStringOf("x"));
		assertTrue(1 <= firstX.val && firstX.val <= 100000000);
		final IntValue firstY = (IntValue) firstState.get(UniqueString.uniqueStringOf("y"));
		assertTrue(100000000 <= firstY.val && firstX.val <= 100000010);

		// Check z is true
		assertEquals(BoolValue.ValTrue, (IBoolValue) firstState.get(UniqueString.uniqueStringOf("z")));
		
		final TLCStateInfo second = (TLCStateInfo) ((Object[]) actual.get(1))[0];
		assertTrue(((String) second.info).startsWith("<_next line 33, col 5 to line 41, col 29 of module "+getModuleName()+">"));
		final Map<UniqueString, IValue> secondState = second.state.getVals();
		assertEquals(3, secondState.size());
		// UNCHANGED x,y
		assertEquals(firstX.val, ((IntValue) secondState.get(UniqueString.uniqueStringOf("x"))).val);
		assertEquals(firstY.val, ((IntValue) secondState.get(UniqueString.uniqueStringOf("y"))).val);
		// Check z is false
		assertEquals(BoolValue.ValFalse, (IBoolValue) secondState.get(UniqueString.uniqueStringOf("z")));

		assertZeroUncovered();
	}
}
