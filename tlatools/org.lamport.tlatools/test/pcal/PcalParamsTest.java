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
package pcal;

import static org.junit.Assert.*;

import org.junit.Test;
import java.io.File;
import java.io.IOException;
import org.junit.BeforeClass;
import org.junit.AfterClass;

public class PcalParamsTest {

	private static File testFile;

	@BeforeClass
	public static void setUpClass() throws IOException {
		// Create a test file in the system's temp directory
		testFile = File.createTempFile("dummy", ".tla");
		testFile.deleteOnExit(); // Ensure cleanup if JVM exits unexpectedly
	}

	@AfterClass
	public static void tearDownClass() {
		if (testFile != null && testFile.exists()) {
			testFile.delete();
		}
	}

	@Test
	public void test() {
		assertNotSame(PcalParams.version, "1.9");
		assertTrue(PcalParams.versionWeight > PcalParams.VersionToNumber("1.9"));
	}

	@Test
	public void testLabelRootValid() throws IOException {
		String[] validCases = {
			"validName",     // standard identifier with letters
			"a1",           // letter followed by number
			"A_1",          // letter followed by underscore and number
			"abc123_456"    // complex mix of letters, numbers, and underscores
		};

		for (String valid : validCases) {
			assertEquals("Valid identifier should be accepted: " + valid,
				trans.STATUS_OK,
				trans.parseAndProcessArguments(new String[] {"-labelRoot", valid, testFile.getAbsolutePath()}));
		}
	}

	@Test
	public void testLabelRootInvalid() throws IOException {
		String[] invalidCases = {
			"1abc",    // starts with number
			"_abc",    // starts with underscore
			"123",     // only numbers
			"_",       // only underscore
			""        // empty string
		};

		for (String invalid : invalidCases) {
			int result = trans.parseAndProcessArguments(new String[] {"-labelRoot", invalid, testFile.getAbsolutePath()});
			assertEquals("Invalid identifier should be rejected: " + invalid,
				trans.STATUS_EXIT_WITH_ERRORS, result);
		}
	}
}
