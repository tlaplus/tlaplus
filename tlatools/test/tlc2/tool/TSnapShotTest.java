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

package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class TSnapShotTest extends ModelCheckerTestCase {

	public TSnapShotTest() {
		super("MC", "TSnapShot");
	}
	
	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertFalse(recorder.recorded(EC.TLC_BUG));

		assertTrue(recorder.recorded(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT));

		assertCoverage("  line 102, col 30 to line 103, col 67 of module TSnapShot: 0\n" +
			"  line 111, col 26 to line 112, col 40 of module TSnapShot: 0\n" +
			"  line 118, col 26 to line 119, col 40 of module TSnapShot: 0\n" +
			"  line 129, col 51 to line 129, col 57 of module TSnapShot: 0\n" +
			"  line 134, col 37 to line 134, col 42 of module TSnapShot: 0\n" +
			"  line 141, col 30 to line 141, col 59 of module TSnapShot: 0\n" +
			"  line 148, col 31 to line 148, col 91 of module TSnapShot: 0\n" +
			"  line 154, col 28 to line 155, col 44 of module TSnapShot: 0\n" +
			"  line 159, col 29 to line 160, col 60 of module TSnapShot: 0\n" +
			"  line 87, col 28 to line 87, col 63 of module TSnapShot: 88\n" +
			"  line 96, col 36 to line 96, col 78 of module TSnapShot: 9");
	}
	
	protected int getNumberOfThreads() {
		// This bug only shows up with multiple threads.
		return 4;
	}
}
