/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved. 
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
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.value.IValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.TupleValue;
import util.UniqueString;

public class RandomSubsetNextTuplesTest extends ModelCheckerTestCase {

	public RandomSubsetNextTuplesTest() {
		super("RandomSubsetNextTuples", ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.TLC_BUG));
		assertFalse(recorder.recorded(EC.GENERAL));

		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "4"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "5461", "5461", "4095"));

		assertTrue(recorder.recorded(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT));

		final List<Object> records = recorder.getRecords(EC.TLC_STATE_PRINT2);
		assertEquals(7, records.size());

		int y = 0;
		for (Object record : records) {
			final Object[] objs = (Object[]) record;
			final Map<UniqueString, IValue> vals = ((TLCStateInfo) objs[0]).state.getVals();

			assertEquals(y++, ((IntValue) vals.get(UniqueString.uniqueStringOf("y"))).val);
			assertEquals(y, objs[1]);

			assertTupleIn(vals.get(UniqueString.uniqueStringOf("p")), 200);
			assertTupleIn(vals.get(UniqueString.uniqueStringOf("q")), 4000);
		}

		assertZeroUncovered();
	}

	private static void assertTupleIn(final IValue value, final int n) {
		final TupleValue tuple = (TupleValue) value;
		assertEquals(3, tuple.elems.length);
		for (int i = 0; i < tuple.elems.length; i++) {
			final int component = ((IntValue) tuple.elems[i]).val;
			assertTrue(1 <= component && component <= n);
		}
	}
}
