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
package tlc2.tool.liveness;

import static org.junit.Assert.assertFalse;

import java.io.File;

import org.junit.Test;

import tlc2.output.EC;

public class TwoPhaseCommitTest extends ModelCheckerTestCase {

	public TwoPhaseCommitTest() {
		super("MC", "symmetry" + File.separator + "TwoPhaseCommit");
	}
	
	@Test
	public void testSpec() {
		assertFalse(recorder.recorded(EC.GENERAL));

	assertCoverage("  line 105, col 6 to line 105, col 24 of module TwoPhaseCommit: 1060\n" +
		"  line 106, col 6 to line 106, col 32 of module TwoPhaseCommit: 1060\n" +
		"  line 107, col 16 to line 107, col 36 of module TwoPhaseCommit: 0\n" +
		"  line 75, col 59 to line 75, col 87 of module TwoPhaseCommit: 355\n" +
		"  line 75, col 9 to line 75, col 54 of module TwoPhaseCommit: 355\n" +
		"  line 76, col 58 to line 76, col 85 of module TwoPhaseCommit: 355\n" +
		"  line 76, col 9 to line 76, col 53 of module TwoPhaseCommit: 355\n" +
		"  line 77, col 16 to line 77, col 36 of module TwoPhaseCommit: 0\n" +
		"  line 83, col 30 to line 83, col 73 of module TwoPhaseCommit: 30\n" +
		"  line 84, col 29 to line 84, col 70 of module TwoPhaseCommit: 2700\n" +
		"  line 85, col 16 to line 85, col 42 of module TwoPhaseCommit: 0\n" +
		"  line 93, col 6 to line 93, col 36 of module TwoPhaseCommit: 640\n" +
		"  line 95, col 14 to line 95, col 34 of module TwoPhaseCommit: 1\n" +
		"  line 96, col 14 to line 96, col 41 of module TwoPhaseCommit: 1\n" +
		"  line 97, col 21 to line 97, col 36 of module TwoPhaseCommit: 0\n" +
		"  line 98, col 6 to line 98, col 21 of module TwoPhaseCommit: 640");
	}
}
