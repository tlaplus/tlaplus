/*******************************************************************************
 * Copyright (c) 2025 Microsoft. All rights reserved. 
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

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github1147Test extends ModelCheckerTestCase {
	
	private static final Path dumpFilePath = Paths.get(System.getProperty("java.io.tmpdir"), "Github1147.dot");

	public Github1147Test() {
		super("Github1147",
				new String[] { "-dump", "dot,actionLabels,colorize", Github1147Test.dumpFilePath.toString() },
				ExitStatus.VIOLATION_SAFETY);
	}

	@Test
	public void testSpec() throws FileNotFoundException, IOException {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "51", "50", "47"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "3"));
		
		// Assert POSTCONDITION.
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_FALSE));
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_EVALUATION_ERROR));

		assertTrue(Files.exists(Github1147Test.dumpFilePath));
		
		// If the file exist, simply compare it to a correct and manually checked version.
		try (final InputStream expected = getClass().getResourceAsStream("Github1147.dot");
				final FileInputStream actual = new FileInputStream(Github1147Test.dumpFilePath.toFile());) {
			BufferedReader expectedReader = new BufferedReader(new InputStreamReader(expected));
			BufferedReader actualReader = new BufferedReader(new InputStreamReader(actual));
			while (expectedReader.ready() && actualReader.ready()) {
				String expectedLine = expectedReader.readLine();
				String actualLine = actualReader.readLine();
				assertEquals(expectedLine, actualLine);
			}

			assertEquals(expectedReader.ready(), actualReader.ready());
		}

		assertZeroUncovered();
		
	}

	@Override
	protected boolean doDump() {
		// Create the non-dot dump explicitly through constructor above.
		return false;
	}
}
