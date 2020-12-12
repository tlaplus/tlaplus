/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
import static org.junit.Assert.assertTrue;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.stream.Stream;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github407Test extends ModelCheckerTestCase {
	
	private static final Path dumpFilePath = Paths.get(System.getProperty("java.io.tmpdir"), "Github407.dump");

	public Github407Test() {
		super("Github407",
				new String[] { "-dump", Github407Test.dumpFilePath.toString() },
				ExitStatus.SUCCESS);
	}

	@Test
	public void testSpec() throws FileNotFoundException, IOException {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "9", "4", "0"));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "3"));
		
		assertTrue(Files.exists(Github407Test.dumpFilePath));
		
		// If the file exist, simply compare it to a correct and manually checked version.
		try (
			final InputStream expected = getClass().getResourceAsStream("Github407.dump");
			final FileInputStream actual = new FileInputStream(Github407Test.dumpFilePath.toFile());
			) {
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
