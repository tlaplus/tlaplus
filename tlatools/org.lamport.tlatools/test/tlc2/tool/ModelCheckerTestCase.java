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
package tlc2.tool;

import org.junit.After;
import org.junit.Before;
import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.output.MP;
import tlc2.tool.CommonTestCase;
import tlc2.tool.ModelChecker;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.TLCStateMutExt;
import tlc2.tool.liveness.GraphNode;
import tlc2.tool.liveness.TTraceModelCheckerTestCase;
import tlc2.util.BufferedRandomAccessFile;
import util.FileUtil;
import util.FilenameToStream;
import util.SimpleFilenameToStream;
import util.ToolIO;

import java.io.File;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;

import static org.junit.Assert.*;

public abstract class ModelCheckerTestCase extends CommonTestCase {

    protected static final String DUMP_DOT = System.getProperty("tlc2.test.dump", "true");
    protected String path = "";
    protected String spec;
    protected String[] extraArguments = new String[0];
    protected TLC tlc;
    protected int actualExitStatus = -1;
    protected int expectedExitStatus = ExitStatus.SUCCESS;

    public ModelCheckerTestCase(final String spec) {
        this(spec, ExitStatus.SUCCESS);
    }

    public ModelCheckerTestCase(final String spec, final int exitStatus) {
        this(spec, "", exitStatus);
    }

    public ModelCheckerTestCase(final String spec, final String path) {
        this(spec, path, ExitStatus.SUCCESS);
    }

    public ModelCheckerTestCase(final String spec, final String[] extraArguments) {
        this(spec, "", extraArguments, ExitStatus.SUCCESS);
    }

    public ModelCheckerTestCase(final String spec, final String[] extraArguments, final int exitStatus) {
        this(spec, "", extraArguments, exitStatus);
    }

    public ModelCheckerTestCase(final String spec, final String path, final String[] extraArguments) {
        this(spec, path, extraArguments, ExitStatus.SUCCESS);
    }

    public ModelCheckerTestCase(final String spec, final String path, final String[] extraArguments, final int exitStatus) {
        this(spec, path, exitStatus);
        this.extraArguments = extraArguments;
    }

    public ModelCheckerTestCase(final String spec, final String path, final int exitStatus) {
        super(new TestMPRecorder());
        this.spec = spec;
        this.path = path;
        this.expectedExitStatus = exitStatus;
    }

    protected boolean isExtendedTLCState() {
        return tlc.tool.getEmptyState() instanceof TLCStateMutExt;
    }

    /**
     * Asserts that the actual trace and the expected error trace are equal.
     *
     * @param actual        The actual trace as recorded by {@link tlc2.TestMPRecorder}.
     * @param expectedTrace The expected trace.
     */
    protected void assertTraceWith(final List<Object> actual, final List<String> expectedTrace) {
        assertEquals(expectedTrace.size(), actual.size());
        for (int i = 0; i < expectedTrace.size(); i++) {
            final Object[] objs = (Object[]) actual.get(i);
            final TLCStateInfo stateInfo = (TLCStateInfo) objs[0];
            final String info = (String) stateInfo.info;
            if (i == 0 && !isExtendedTLCState()) {
                // The first state has to be an initial state.
                assertEquals("<Initial predicate>", info);
            } else {
                // ... all others are reachable via an action.
                //TODO: Assert actual action names.
                assertNotEquals("<Initial predicate>", info);
                //assertFalse(info.startsWith("<Action")); Some traces will be for unknown actions
            }
            assertEquals(expectedTrace.get(i),
                    stateInfo.toString().trim()); // trimmed to remove any newlines or whitespace
            assertEquals(i + 1, objs[1]);
        }
    }

    protected void assertTraceWithSingleTrace(final List<Object> actual, String expectedTrace) {
        int i = 0;
        final Object[] objs = (Object[]) actual.get(i);
        final TLCStateInfo stateInfo = (TLCStateInfo) objs[0];
        final String info = (String) stateInfo.info;
        if (i == 0 && !isExtendedTLCState()) {
            // The first state has to be an initial state.
            assertEquals("<Initial predicate>", info);
        } else {
            // ... all others are reachable via an action.
            //TODO: Assert actual action names.
            assertNotEquals("<Initial predicate>", info);
            assertFalse(info.startsWith("<Action"));
        }
        assertEquals(expectedTrace,
                stateInfo.toString().trim()); // trimmed to remove any newlines or whitespace
        assertEquals(i + 1, objs[1]);
    }

    /**
     * Check the file size of the AbstractDiskGraph files to assert that the
     * expected amount of ptrs and nodes (outgoing arcs) have been written to
     * disk.
     * <p>
     * CAUTION: The order in which the transitions are inserted into the
     * {@link GraphNode} determines the size of the {@link BitSet}. I.e. if
     * the truth values of the first N nodes inserted are true, and the
     * remainder is false, the BitSet's size will correspond to N. However,
     * if the first N truth values are false, followed by M trues, the
     * BitSet's size is N + M.
     * <p>
     * See {@link GraphNode}'s constructor: it initializes {@link BitSet}
     * with capacity zero and subsequently grows BV when bits are set to true.
     * <p>
     *
     * @see tlc2.util.BitSetUtilities#fromFile
     * @see tlc2.util.BitSetUtilities#write
     * @see GraphNode#read(BufferedRandomAccessFile)
     * @see GraphNode#write(BufferedRandomAccessFile)
     */
    protected void assertNodeAndPtrSizes(final long nodesSize, final long ptrsSize) {
        final String metadir = tlc.mainChecker.metadir;
        assertNotNull(metadir);

        final File nodes = new File(metadir + File.separator + "nodes_0");
        assertTrue(nodes.exists());
        assertEquals(nodesSize, nodes.length());

        final File ptrs = new File(metadir + File.separator + "ptrs_0");
        assertTrue(ptrs.exists());
        assertEquals(ptrsSize, ptrs.length());
    }

    protected void beforeSetUp() {
        // No-op
    }

    /* (non-Javadoc)
     * @see junit.framework.TestCase#setUp()
     */
    @Before
    public void setUp() {
        beforeSetUp();


        // some tests might want to access the liveness graph after model
        // checking completed. Thus, prevent the liveness graph from being
        // closed too earlier.
        System.setProperty(ModelChecker.class.getName() + ".vetoCleanup", "true");

        try {
            var userDir = TEST_MODEL_PATH + path;

            // TEST_MODEL is where TLC should look for user defined .tla files
            ToolIO.setUserDir(userDir);

            MP.setRecorder(recorder);

            // Increase the liveness checking threshold to prevent liveness
            // checking of an incomplete graph. Most tests check that the
            // state queue is empty and fail if not. This is only given
            // when liveness checking is executed when all states have been
            // generated.
            TLCGlobals.livenessThreshold = getLivenessThreshold();

            tlc = new TLC();
            tlc.setResolver(getResolver());
            // * We want *no* deadlock checking to find the violation of the
            // temporal formula
            // * We use (unless overridden) a single worker to simplify
            // debugging by taking out threading
            // * MC is the name of the TLA+ specification to be checked (the file
            // is placed in TEST_MODEL
            final List<String> args = new ArrayList<>(6);

            // *Don't* check for deadlocks. All tests are interested in liveness
            // checks which are shielded away by deadlock checking. TLC finds a
            // deadlock (if it exists) before it finds most liveness violations.
            if (!checkDeadLock()) {
                args.add("-deadlock");
            }

            if (getNumberOfThreads() == 1 && collectStateInfo()) {
                args.add("-collectStateInfo");
                //args.add(String.format("nosuspend,port=%s,nohalt", 1025 + new Random().nextInt(64540)));
            }

            if (noGenerateSpec()) {
                args.add("-noGenerateSpecTE");
            } else {
                // Make sure the generated spec ends up in a designated location.
                args.add("-generateSpecTE");
                args.add("-teSpecOutDir");
                args.add(TTraceModelCheckerTestCase.getTESpecPath(getClass()));
            }

            if (noRandomFPandSeed()) {
                args.add("-fp");
                args.add("0");
                // Deterministic simulation (order in which actions are explored).
                args.add("-seed");
                args.add("1");
            }

            if (doCoverage()) {
                args.add("-coverage");
                args.add("1");
            }

            args.add("-workers");
            args.add(Integer.toString(getNumberOfThreads()));

            // Never create checkpoints. They distort performance tests and are
            // of no use anyway.
            args.add("-checkpoint");
            args.add(Integer.toString(doCheckpoint()));

            // Always print the state graph in dot file notation.
            if (doDump()) {
                args.add("-dump");
                args.add("dot");
                args.add("${metadir}" + FileUtil.separator + getClass().getCanonicalName() + ".dot");
            }


            if (doDumpTrace()) {
                args.add("-dumpTrace");
                args.add("json");
                args.add(TLCGlobals.metaRoot + FileUtil.separator + getClass().getCanonicalName() + ".json");
            }

            args.addAll(Arrays.asList(extraArguments));

            args.add(spec);
            tlc.handleParameters(args.toArray(new String[0]));

            // Run the ModelChecker
            final int errorCode = tlc.process();
            actualExitStatus = EC.ExitStatus.errorConstantToExitStatus(errorCode);

        } catch (final Exception e) {
            fail(e.getMessage());
        }
    }

    protected boolean noRandomFPandSeed() {
        return true;
    }

    protected boolean collectStateInfo() {
        return false; // to prevent memory leak
    }

    protected double getLivenessThreshold() {
        return Double.MAX_VALUE;
    }

    protected FilenameToStream getResolver() {
        return new SimpleFilenameToStream();
    }

    protected boolean noGenerateSpec() {
        return false;
    }

    protected void beforeTearDown() {
        // No-op
    }

    @After
    public void tearDown() {
        beforeTearDown();

        // Uncomment to print out the full recorder to stdout
        //ToolIO.out.println(recorder.toString());

        // Cleanup by unsubscribing
        MP.unsubscribeRecorder(recorder);

        tlc = null;
        System.gc();

        assertExitStatus();
    }

    protected void assertExitStatus() {
        assertEquals(expectedExitStatus, actualExitStatus);
    }

    protected boolean doCoverage() {
        return true;
    }

    /**
     * @return True if TLC is to be called with "-deadlock".
     */
    protected boolean checkDeadLock() {
        return false;
    }

    protected boolean doDump() {
        return DUMP_DOT.equals("true");
    }

    protected boolean doDumpTrace() {
        return true;
    }

    protected int doCheckpoint() {
        return 0;
    }

    /**
     * @return The number of worker threads TLC should use.
     */
    protected int getNumberOfThreads() {
        return 1;
    }

    protected void setExitStatus(final int exitStatus) {
        this.expectedExitStatus = exitStatus;
    }

    /**
     * E.g.
     * ILiveCheck liveCheck = (ILiveCheck) getField(AbstractChecker.class, "liveCheck",
     * getField(TLC.class, "instance", tlc));
     */
    protected Object getField(final Class<?> targetClass, final String fieldName, final Object instance) {
        try {
            final Field field = targetClass.getDeclaredField(fieldName);
            field.setAccessible(true);
            return field.get(instance);
        } catch (final NoSuchFieldException | IllegalAccessException | IllegalArgumentException | SecurityException e) {
            e.printStackTrace();
        }
        return null;
    }
}
