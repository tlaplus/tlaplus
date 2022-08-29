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

import org.junit.Test;
import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Objects;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

public class Github407Test extends ModelCheckerTestCase {

    private static final Path dumpFilePath = Paths.get(System.getProperty("java.io.tmpdir"), "Github407.dump");

    public Github407Test() {
        super("Github407",
                new String[]{"-dump", Github407Test.dumpFilePath.toString()},
                ExitStatus.SUCCESS);
    }

    @Test
    public void testSpec() throws IOException {
        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "9", "4", "0"));
        assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "3"));

        assertTrue(Files.exists(Github407Test.dumpFilePath));

        // If the file exist, simply compare it to a correct and manually checked version.
        try (
                final InputStream expected = getClass().getResourceAsStream("Github407.dump");
                final FileInputStream actual = new FileInputStream(Github407Test.dumpFilePath.toFile())
        ) {
            final BufferedReader expectedReader = new BufferedReader(new InputStreamReader(Objects.requireNonNull(expected)));
            final BufferedReader actualReader = new BufferedReader(new InputStreamReader(actual));
            while (expectedReader.ready() && actualReader.ready()) {
                final String expectedLine = expectedReader.readLine();
                final String actualLine = actualReader.readLine();
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
