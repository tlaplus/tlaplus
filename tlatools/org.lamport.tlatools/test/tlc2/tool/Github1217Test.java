/*******************************************************************************
 * Copyright (c) 2024 Microsoft Research. All rights reserved.
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
 *   Anatoliy Bilenko - initial implementation
 ******************************************************************************/
package tlc2.tool;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertEquals;

import java.io.IOException;
import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.Files;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.FileUtil;


public class Github1217Test extends ModelCheckerTestCase {

	private static final Path dumpFilePath = Paths.get(System.getProperty("java.io.tmpdir"), "Github1217.json");

	public Github1217Test() {
		super("Github1217", new String[] { "-note", "-config", "Github1217.cfg", "-simulate", "-invlevel", "10",
						  				  "-dumpTrace", "json", dumpFilePath.toString(), "Github1217.tla"},
		EC.ExitStatus.VIOLATION_SAFETY);
	}

	@Override
 	protected boolean runWithDebugger() {
 		return false;
 	}
	@Test
	public void testSpec() throws IOException {
	  	assertTrue(recorder.recorded(EC.TLC_FINISHED));

		// Assert POSTCONDITION.
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_FALSE));
		assertFalse(recorder.recorded(EC.TLC_ASSUMPTION_EVALUATION_ERROR));

		assertTrue(Files.exists(Github1217Test.dumpFilePath));

		try (
				final InputStream expected = getClass().getResourceAsStream("Github1217.dump");
				final FileInputStream actual = new FileInputStream(Github1217Test.dumpFilePath.toFile());
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
}
