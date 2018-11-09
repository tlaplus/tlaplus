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

public class PetersonTest extends PCalModelCheckerTestCase {

	public PetersonTest() {
		super("Peterson", "pcal");
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "85", "42", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "11"));

	assertCoverage("  line 52, col 16 to line 52, col 47 of module Peterson: 18\n" +
		"  line 53, col 26 to line 53, col 41 of module Peterson: 0\n" +
		"  line 56, col 16 to line 56, col 51 of module Peterson: 18\n" +
		"  line 57, col 16 to line 57, col 47 of module Peterson: 18\n" +
		"  line 58, col 16 to line 58, col 27 of module Peterson: 18\n" +
		"  line 61, col 16 to line 61, col 32 of module Peterson: 18\n" +
		"  line 62, col 16 to line 62, col 47 of module Peterson: 18\n" +
		"  line 63, col 16 to line 63, col 27 of module Peterson: 18\n" +
		"  line 68, col 27 to line 68, col 58 of module Peterson: 8\n" +
		"  line 69, col 27 to line 69, col 58 of module Peterson: 6\n" +
		"  line 70, col 26 to line 70, col 41 of module Peterson: 0\n" +
		"  line 74, col 16 to line 74, col 47 of module Peterson: 8\n" +
		"  line 75, col 26 to line 75, col 41 of module Peterson: 0\n" +
		"  line 78, col 16 to line 78, col 52 of module Peterson: 8\n" +
		"  line 79, col 16 to line 79, col 47 of module Peterson: 8\n" +
		"  line 80, col 16 to line 80, col 27 of module Peterson: 8");
	}
}
