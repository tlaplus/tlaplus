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
import tlc2.value.IValue;
import tlc2.value.impl.IntValue;
import util.UniqueString;

public class RandomSubsetNextT4Test_TTraceTest extends TTraceModelCheckerTestCase {

	public RandomSubsetNextT4Test_TTraceTest() {
		super(RandomSubsetNextT4Test.class, ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.TLC_BUG));

		assertTrue(recorder.recorded(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT));
		
		final List<Object> records = recorder.getRecords(EC.TLC_STATE_PRINT2);
		assertEquals(11, records.size());
		
		int cnt = 0;
		for (Object r : records) {
			final Object[] objs = (Object[]) r;
			final TLCStateInfo info = (TLCStateInfo) objs[0];
			final Map<UniqueString, IValue> vals = info.state.getVals();

			final IValue y = vals.get(UniqueString.uniqueStringOf("y"));
			assertEquals(cnt++, ((IntValue) y).val);
			
			final IValue x = info.state.getVals().get(UniqueString.uniqueStringOf("x"));
			assertTrue(1 <= ((IntValue) x).val && ((IntValue) x).val <= 1000);
			
			final int statenum = (int) objs[1];
			assertEquals(cnt, statenum);
		}
	}
	
	protected int getNumberOfThreads() {
		// With 4 threads the counter-examples is not predictable anymore because it
		// depends on thread scheduling.
		return 4;
	}
}
