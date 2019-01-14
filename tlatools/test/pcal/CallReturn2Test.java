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
package pcal;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;

public class CallReturn2Test extends PCalModelCheckerTestCase {

	public CallReturn2Test() {
		super("CallReturn2", "pcal", new String[] {"-wf", "-termination"});
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKING_TEMPORAL_PROPS, "complete", "11"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "12", "11", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "11"));
		
		assertUncovered("  line 129, col 10 to line 129, col 15 of module CallReturn2: 0\n" + 
				"  line 130, col 10 to line 130, col 19 of module CallReturn2: 0\n" + 
				"  line 131, col 10 to line 131, col 65 of module CallReturn2: 0\n" + 
				"  line 134, col 13 to line 134, col 18 of module CallReturn2: 0\n" + 
				"  line 135, col 13 to line 138, col 36 of module CallReturn2: 0\n" + 
				"  line 139, col 13 to line 139, col 30 of module CallReturn2: 0\n" + 
				"  line 140, col 10 to line 140, col 19 of module CallReturn2: 0\n" + 
				"  line 141, col 10 to line 141, col 55 of module CallReturn2: 0\n" + 
				"  line 147, col 10 to line 147, col 29 of module CallReturn2: 0\n" + 
				"  line 148, col 10 to line 148, col 27 of module CallReturn2: 0\n" + 
				"  line 149, col 10 to line 149, col 29 of module CallReturn2: 0\n" + 
				"  line 150, col 10 to line 150, col 58 of module CallReturn2: 0");
	}
}
