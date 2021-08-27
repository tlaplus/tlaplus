/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved.
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
 *   Markus Alexander Kuppe - initial design and implementation
 ******************************************************************************/

package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class FingerprintExceptionNextCallstackTest extends ModelCheckerTestCase {

	public FingerprintExceptionNextCallstackTest() {
		super("FingerprintExceptionNextCallstack", new String[] { "-config", "FingerprintExceptionNext.cfg" },
				ExitStatus.FAILURE_SPEC_EVAL);
	}

	@Test
	public void testSpec() {
		// ModelChecker has finished with a general exception, a fingerprint exception and underlying overflow exception
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "1", "1", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INIT_GENERATED1, "1"));
		assertTrue(recorder.recorded(EC.GENERAL));
		String arg1 = "0. Line 9, column 9 to line 9, column 19 in FingerprintExceptionNextCallstack\n"
				+ "1. Line 9, column 14 to line 9, column 19 in FingerprintExceptionNextCallstack\n"
				+ "2. Line 7, column 10 to line 7, column 49 in FingerprintExceptionNextCallstack\n"
				+ "3. Line 7, column 43 to line 7, column 49 in FingerprintExceptionNextCallstack\n"
				+ "4. Line 7, column 25 to line 7, column 32 in FingerprintExceptionNextCallstack\n\n";
		String arg2 = "Attempted to check if the non-enumerable value\n"
				+ "42\n"
				+ "is element of\n"
				+ "SUBSET 42";
		assertTrue(recorder.recordedWithStringValues(EC.TLC_FINGERPRINT_EXCEPTION, arg1, arg2));
	}
}
