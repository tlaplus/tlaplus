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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.List;

import org.junit.Test;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.value.IValue;
import tlc2.value.impl.IntValue;

public class PostConditionsTest extends ModelCheckerTestCase {

	public PostConditionsTest() {
		super("PostConditionsTest");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertFalse(recorder.recorded(EC.TLC_POSTCONDITION_FALSE));
		assertFalse(recorder.recorded(EC.TLC_POSTCONDITION_EVALUATION_ERROR));

		final List<IValue> reg100 = TLCGlobals.mainChecker.getAllValue(100);
		assertTrue("Post1 was not evaluated: register 100 is empty", !reg100.isEmpty());
		assertTrue("Post1 did not write generated count",
				reg100.get(0) instanceof IntValue && ((IntValue) reg100.get(0)).val == 4);

		final List<IValue> reg101 = TLCGlobals.mainChecker.getAllValue(101);
		assertTrue("Post2 was not evaluated: register 101 is empty", !reg101.isEmpty());
		assertTrue("Post2 did not write distinct count",
				reg101.get(0) instanceof IntValue && ((IntValue) reg101.get(0)).val == 4);
	}
}
