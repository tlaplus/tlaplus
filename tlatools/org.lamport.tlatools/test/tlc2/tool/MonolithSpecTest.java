/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.regex.Pattern;

import org.junit.Before;
import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.TestPrintStream;
import util.ToolIO;

public class MonolithSpecTest extends ModelCheckerTestCase {
        final TestPrintStream testPrintStreamErr = new TestPrintStream();
		final TestPrintStream testPrintStreamOut = new TestPrintStream();

	public MonolithSpecTest() {
		super("MonolithSpec", new String[] { "-config", "MonolithSpec.tla" /* note the extension */ });
	}

        @Before
        public void beforeSetUp() {
            ToolIO.err = testPrintStreamErr;
			ToolIO.out = testPrintStreamOut;
            ToolIO.reset();
        }

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "214", "54", "0"));

        // Check that the warning or inexistent file does not occur.
        testPrintStreamErr.assertNoSubstring("File does not exist");

		// Test that the library path appears between `( )` after parsing the file.		
		final String sep = Pattern.quote(File.separator);
		testPrintStreamOut.assertRegex("Parsing file .*" + sep + "EWD840.tla \\(.*" + sep + "test-model" + sep + "MonolithSpec.tla\\)");
		testPrintStreamOut.assertRegex("Parsing file .*" + sep + "Mod4711.tla \\(.*" + sep + "test-model" + sep + "MonolithSpec.tla\\)");
		testPrintStreamOut.assertRegex("Parsing file .*" + sep + "Mod4712.tla \\(.*" + sep + "test-model" + sep + "MonolithSpec.tla\\)");

		assertZeroUncovered();
	}
}
