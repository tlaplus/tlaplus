/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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

import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.BlockJUnit4ClassRunner;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

@RunWith(BlockJUnit4ClassRunner.class)
public class UserModuleOverrideTest extends ModelCheckerTestCase {

	public UserModuleOverrideTest() {
		super("UserModuleOverride");
	}
	
	@Test
	public void testSpec() {
		final List<String[]> mismatches = recorder.getRecordAsStringArray(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MISMATCH);
		assertEquals(2, mismatches.size());
		Collections.sort(mismatches, new Comparator<String[]>() {
			@Override
			public int compare(String[] o1, String[] o2) {
				return o1[0].compareTo(o2[0]);
			}
		});
		
		// arity mismatch
		String[] strs = mismatches.get(0);
		assertEquals("Get2", strs[0]);
		assertTrue(strs[1].endsWith("UserModuleOverride.class")); // This contains a system dependent path.
		assertEquals("<Java Method: public static tlc2.value.impl.Value UserModuleOverride.Get2(tlc2.value.impl.Value)>", strs[2]);
		
		// name mismatch (no such operator)
		strs = mismatches.get(1);
		assertEquals("Get3", strs[0]);
		assertTrue(strs[1].endsWith("UserModuleOverride.class"));
		assertEquals("<Java Method: public static tlc2.value.impl.Value UserModuleOverride.Get3()>", strs[2]);

		// ModelChecker has finished and generated the expected amount of states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2", "1", "0"));
		assertFalse(recorder.recorded(EC.GENERAL));

		assertZeroUncovered();
	}
}
