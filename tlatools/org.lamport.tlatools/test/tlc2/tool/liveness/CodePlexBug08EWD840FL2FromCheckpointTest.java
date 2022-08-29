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

package tlc2.tool.liveness;

import org.junit.Test;
import org.junit.experimental.categories.Category;
import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.ModelCheckerTestCase;
import util.IndependentlyRunTest;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.zip.ZipEntry;
import java.util.zip.ZipFile;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * see <a href="http://tlaplus.codeplex.com/workitem/8">...</a>
 */
public class CodePlexBug08EWD840FL2FromCheckpointTest extends ModelCheckerTestCase {

    public CodePlexBug08EWD840FL2FromCheckpointTest() {
        super("EWD840MC2", "CodePlexBug08", new String[]{"-gzip", "-recover", TEST_MODEL_PATH + "CodePlexBug08" + File.separator + "checkpoint"}, ExitStatus.VIOLATION_LIVENESS);
    }


    @Override
    public void setUp() {
        try {
            /* Recreate checkpoint.zip whenever file format changes:
             *
             * 1) Run CodePlexBug08EWD840FL2Test with "-gzip"
             * 2) Connect to running test via JMX and request TLC checkpoint to be taken
             * 3) Terminate CodePlexBug08EWD840FL2Test once checkpoint successfully taken
             * 4) Locate the directory with the checkpoint data
             * 5) Replace the content of checkpoint.zip with the content of 4)
             * 6) Update the number below on states found...
             */
            final String prefix = TEST_MODEL_PATH + "CodePlexBug08" + File.separator;
            final ZipFile zipFile = new ZipFile(prefix + "checkpoint.zip");
            final Enumeration<?> enu = zipFile.entries();
            while (enu.hasMoreElements()) {
                final ZipEntry zipEntry = (ZipEntry) enu.nextElement();

                final File file = new File(prefix + zipEntry.getName());
                if (zipEntry.getName().endsWith("/")) {
                    file.mkdirs();
                    continue;
                }

                final File parent = file.getParentFile();
                if (parent != null) {
                    parent.mkdirs();
                }

                final InputStream is = zipFile.getInputStream(zipEntry);
                final FileOutputStream fos = new FileOutputStream(file);
                final byte[] bytes = new byte[1024];
                int length;
                while ((length = is.read(bytes)) >= 0) {
                    fos.write(bytes, 0, length);
                }
                is.close();
                fos.close();

            }
            zipFile.close();
        } catch (final IOException e) {
            e.printStackTrace();
        }
        super.setUp();
    }

    @Category(IndependentlyRunTest.class)
    @Test
    public void testSpec() {
        assertTrue(recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_START));
        // Recovery completed. 1032 states examined. 996 states on queue.
        assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKPOINT_RECOVER_END, "1510", "39"));
        // ModelChecker has finished and generated the expected amount of states
        assertTrue(recorder.recorded(EC.TLC_FINISHED));
        assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "2334", "1566", "0"));
        assertFalse(recorder.recorded(EC.GENERAL));

        assertNoTESpec();

        // Assert it has found the temporal violation and also a counter example
        assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
        assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));

        assertNodeAndPtrSizes(54038132L, 831296L);

        // Assert the error trace
        assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
        final List<String> expectedTrace = new ArrayList<>();
        expectedTrace.add("""
                /\\ tpos = 0
                /\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)
                /\\ tcolor = "black"
                /\\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white")""");
        expectedTrace.add("""
                /\\ tpos = 3
                /\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)
                /\\ tcolor = "white"
                /\\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white")""");
        expectedTrace.add("""
                /\\ tpos = 3
                /\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE)
                /\\ tcolor = "white"
                /\\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white")""");
        expectedTrace.add("""
                /\\ tpos = 3
                /\\ active = (0 :> TRUE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE)
                /\\ tcolor = "white"
                /\\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white")""");
        expectedTrace.add("""
                /\\ tpos = 3
                /\\ active = (0 :> TRUE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE)
                /\\ tcolor = "white"
                /\\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white")""");
        expectedTrace.add("""
                /\\ tpos = 3
                /\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE)
                /\\ tcolor = "white"
                /\\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white")""");
        expectedTrace.add("""
                /\\ tpos = 2
                /\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> FALSE)
                /\\ tcolor = "white"
                /\\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white")""");
        expectedTrace.add("""
                /\\ tpos = 2
                /\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE)
                /\\ tcolor = "white"
                /\\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "black" @@ 3 :> "white")""");
        expectedTrace.add("""
                /\\ tpos = 1
                /\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> TRUE @@ 3 :> TRUE)
                /\\ tcolor = "black"
                /\\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white")""");
        expectedTrace.add("""
                /\\ tpos = 1
                /\\ active = (0 :> FALSE @@ 1 :> FALSE @@ 2 :> FALSE @@ 3 :> TRUE)
                /\\ tcolor = "black"
                /\\ color = (0 :> "white" @@ 1 :> "white" @@ 2 :> "white" @@ 3 :> "white")""");
        assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);

        // last state points back to state 1
        assertBackToState(1);
    }


    @Override
    protected int getNumberOfThreads() {
        return 3;
    }


}
