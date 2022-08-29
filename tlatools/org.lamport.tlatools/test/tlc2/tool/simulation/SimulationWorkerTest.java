package tlc2.tool.simulation;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.experimental.categories.Category;
import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.tool.*;
import tlc2.tool.SimulationWorker.SimulationWorkerError;
import tlc2.tool.SimulationWorker.SimulationWorkerResult;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.tool.impl.Tool.Mode;
import tlc2.tool.liveness.ILiveCheck;
import tlc2.tool.liveness.NoOpLiveCheck;
import util.*;

import java.io.File;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.LongAdder;

import static org.junit.Assert.*;

/**
 * Correctness tests for the SimulationWorker.
 */
public class SimulationWorkerTest extends CommonTestCase {

    public SimulationWorkerTest() {
        super(new TestMPRecorder());
    }

    @Before
    public void setUp() {
        ToolIO.setUserDir(TEST_MODEL_PATH + File.separator + "simulation" + File.separator + "BasicMultiTrace");
    }

    @After
    public void tearDown() {
        //FileUtil.deleteDir(TLCGlobals.metaRoot, true);
    }

    /**
     * Return a value from a TLCState as a string.
     */
    public String getStateVal(final TLCState s, final String name) {
        final UniqueString us = UniqueString.uniqueStringOf(name);
        return s.getVals().get(us).toString();
    }

    @Test
    public void testSuccessfulRun() throws Exception {
        final Tool tool = new FastTool("", "BasicMultiTrace", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME, new SimpleFilenameToStream(), Mode.Simulation);

        final ILiveCheck liveCheck = new NoOpLiveCheck(tool, "BasicMultiTrace");
        final StateVec initStates = tool.getInitStates();
        final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();
        final SimulationWorker worker = new SimulationWorker(0, tool, resultQueue, 0, 100, 1000, false, null,
                liveCheck);
        worker.start(initStates);
        final SimulationWorkerResult res = resultQueue.take();
        assertFalse(res.isError());
        worker.join();
        assertFalse(worker.isAlive());
    }

    @Test
    public void testInvariantViolation() throws Exception {
        final Tool tool = new FastTool("", "BasicMultiTrace", "MCInv", new SimpleFilenameToStream(), Mode.Simulation);

        final ILiveCheck liveCheck = new NoOpLiveCheck(tool, "BasicMultiTrace");
        final StateVec initStates = tool.getInitStates();
        final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();
        final int maxTraceNum = 3;
        final SimulationWorker worker = new SimulationWorker(0, tool, resultQueue, 0, 100, maxTraceNum, false,
                null, liveCheck);
        worker.start(initStates);
        SimulationWorkerResult res = resultQueue.take();

        assertTrue(res.isError());
        SimulationWorkerError err = res.error();
        assertEquals(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, err.errorCode);
        assertEquals(3, err.stateTrace.size());

        // Check the generated trace.
        assertEquals("0", getStateVal(err.stateTrace.get(0), "depth"));
        assertEquals("0", getStateVal(err.stateTrace.get(0), "branch"));

        assertEquals("0", getStateVal(err.stateTrace.get(1), "depth"));
        assertEquals("6", getStateVal(err.stateTrace.get(1), "branch"));

        assertEquals("1", getStateVal(err.stateTrace.get(2), "depth"));
        assertEquals("6", getStateVal(err.stateTrace.get(2), "branch"));

        assertEquals("2", getStateVal(err.state, "depth"));
        assertEquals("6", getStateVal(err.state, "branch"));

        // The worker should continue to generate random traces even after an invariant violation, so we should be
        // able to receive more results. The worker should generate 2 more results before hitting the maximum trace count.
        // For the next traces generated, we check their contents to make sure that the worker is actually producing traces
        // "randomly" i.e. not generating the same trace every time.
        res = resultQueue.take();
        assertTrue(res.isError());
        err = res.error();
        assertEquals(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, err.errorCode);
        assertEquals(3, err.stateTrace.size());

        // Check the generated trace.
        assertEquals("0", getStateVal(err.stateTrace.get(0), "depth"));
        assertEquals("0", getStateVal(err.stateTrace.get(0), "branch"));

        assertEquals("0", getStateVal(err.stateTrace.get(1), "depth"));
        assertEquals("2", getStateVal(err.stateTrace.get(1), "branch"));

        assertEquals("1", getStateVal(err.stateTrace.get(2), "depth"));
        assertEquals("2", getStateVal(err.stateTrace.get(2), "branch"));

        res = resultQueue.take();
        assertTrue(res.isError());
        err = res.error();
        assertEquals(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, err.errorCode);
        assertEquals(3, err.stateTrace.size());

        // Check the generated trace.
        assertEquals("0", getStateVal(err.stateTrace.get(0), "depth"));
        assertEquals("0", getStateVal(err.stateTrace.get(0), "branch"));

        assertEquals("0", getStateVal(err.stateTrace.get(1), "depth"));
        assertEquals("5", getStateVal(err.stateTrace.get(1), "branch"));

        assertEquals("1", getStateVal(err.stateTrace.get(2), "depth"));
        assertEquals("5", getStateVal(err.stateTrace.get(2), "branch"));

        // The worker should push one final OK result onto the queue upon termination.
        res = resultQueue.take();
        assertFalse(res.isError());

        worker.join();
        assertFalse(worker.isAlive());
    }

    @Test
    public void testActionPropertyViolation() throws Exception {
        final ITool tool = new FastTool("", "BasicMultiTrace", "MCActionProp", new SimpleFilenameToStream(), Mode.Simulation);

        final StateVec initStates = tool.getInitStates();
        final ILiveCheck liveCheck = new NoOpLiveCheck(tool, "BasicMultiTrace");
        final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();
        final SimulationWorker worker = new SimulationWorker(0, tool, resultQueue, 0, 100, 100, false, null, liveCheck);
        worker.start(initStates);

        SimulationWorkerResult res = resultQueue.take();
        assertTrue(res.isError());
        SimulationWorkerError err = res.error();
        assertEquals(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR, err.errorCode);
        assertEquals(2, err.stateTrace.size());

        // Check the generated trace.
        assertEquals("0", getStateVal(err.stateTrace.get(0), "depth"));
        assertEquals("0", getStateVal(err.stateTrace.get(0), "branch"));

        assertEquals("0", getStateVal(err.stateTrace.get(1), "depth"));
        assertEquals("6", getStateVal(err.stateTrace.get(1), "branch"));

        assertEquals("1", getStateVal(err.state, "depth"));
        assertEquals("6", getStateVal(err.state, "branch"));

        // Check another result.
        res = resultQueue.take();
        assertTrue(res.isError());
        err = res.error();
        assertEquals(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR, err.errorCode);
        assertEquals(2, err.stateTrace.size());

        // Check the generated trace.
        assertEquals("0", getStateVal(err.stateTrace.get(0), "depth"));
        assertEquals("0", getStateVal(err.stateTrace.get(0), "branch"));

        assertEquals("0", getStateVal(err.stateTrace.get(1), "depth"));
        assertEquals("10", getStateVal(err.stateTrace.get(1), "branch"));

        assertEquals("1", getStateVal(err.state, "depth"));
        assertEquals("10", getStateVal(err.state, "branch"));

        worker.join();
        assertFalse(worker.isAlive());
    }

    @Test
    public void testInvariantBadEval() throws Exception {
        final ITool tool = new FastTool("", "BasicMultiTrace", "MCBadInvNonInitState", new SimpleFilenameToStream(), Mode.Simulation);

        final StateVec initStates = tool.getInitStates();
        final ILiveCheck liveCheck = new NoOpLiveCheck(tool, "BasicMultiTrace");
        final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();
        final SimulationWorker worker = new SimulationWorker(0, tool, resultQueue, 0, 100, 100, false, null,
                liveCheck);
        worker.start(initStates);
        final SimulationWorkerResult res = resultQueue.take();

        assertTrue(res.isError());
        final SimulationWorkerError err = res.error();
        assertEquals(EC.TLC_INVARIANT_EVALUATION_FAILED, err.errorCode);
        assertEquals(1, err.stateTrace.size());

        // Check the generated trace.
        assertEquals("0", getStateVal(err.stateTrace.get(0), "depth"));
        assertEquals("0", getStateVal(err.stateTrace.get(0), "branch"));

        assertEquals("0", getStateVal(err.state, "depth"));
        assertEquals("1", getStateVal(err.state, "branch"));

        worker.join();
        assertFalse(worker.isAlive());
    }

    @Test
    public void testActionPropertyBadEval() throws Exception {
        final ITool tool = new FastTool("", "BasicMultiTrace", "MCActionPropBadEval", new SimpleFilenameToStream(), Mode.Simulation);

        final StateVec initStates = tool.getInitStates();
        final ILiveCheck liveCheck = new NoOpLiveCheck(tool, "BasicMultiTrace");
        final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();
        final SimulationWorker worker = new SimulationWorker(0, tool, resultQueue, 0, 100, 100, false, null,
                liveCheck);
        worker.start(initStates);

        final SimulationWorkerResult res = resultQueue.take();

        assertTrue(res.isError());
        final SimulationWorkerError err = res.error();
        assertEquals(EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED, err.errorCode);

        worker.join();
        assertFalse(worker.isAlive());
    }

    @Test
    public void testUnderspecifiedNext() throws Exception {
        final ITool tool = new FastTool("", "BasicMultiTrace", "MCUnderspecNext", new SimpleFilenameToStream(), Mode.Simulation);

        final StateVec initStates = tool.getInitStates();
        final ILiveCheck liveCheck = new NoOpLiveCheck(tool, "BasicMultiTrace");
        final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();
        final SimulationWorker worker = new SimulationWorker(0, tool, resultQueue, 0, 100, 100, false, null,
                liveCheck);
        worker.start(initStates);
        final SimulationWorkerResult res = resultQueue.take();

        assertTrue(res.isError());
        final SimulationWorkerError err = res.error();
        assertEquals(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT, err.errorCode);
        assertEquals(1, err.stateTrace.size());

        // Check the generated trace.
        assertEquals("0", getStateVal(err.stateTrace.get(0), "depth"));
        assertEquals("0", getStateVal(err.stateTrace.get(0), "branch"));

        assertNull(err.state.getVals().get(UniqueString.uniqueStringOf("depth")));
        assertEquals("0", getStateVal(err.state, "branch"));

        worker.join();
        assertFalse(worker.isAlive());
    }

    @Test
    public void testDeadlock() throws Exception {
        final ITool tool = new FastTool("", "BasicMultiTrace", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME, new SimpleFilenameToStream(), Mode.Simulation);

        final StateVec initStates = tool.getInitStates();
        final ILiveCheck liveCheck = new NoOpLiveCheck(tool, "BasicMultiTrace");
        final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();
        final SimulationWorker worker = new SimulationWorker(0, tool, resultQueue, 0, 100, 100, true, null,
                liveCheck);
        worker.start(initStates);
        final SimulationWorkerResult res = resultQueue.take();

        assertTrue(res.isError());
        final SimulationWorkerError err = res.error();
        assertEquals(EC.TLC_DEADLOCK_REACHED, err.errorCode);

        System.out.println(err.stateTrace.toString());
        assertEquals(7, err.stateTrace.size());

        // Check the generated trace.
        assertEquals("0", getStateVal(err.stateTrace.get(0), "depth"));
        assertEquals("0", getStateVal(err.stateTrace.get(0), "branch"));

        assertEquals("0", getStateVal(err.stateTrace.get(1), "depth"));
        assertEquals("6", getStateVal(err.stateTrace.get(1), "branch"));

        assertEquals("1", getStateVal(err.stateTrace.get(2), "depth"));
        assertEquals("6", getStateVal(err.stateTrace.get(2), "branch"));

        assertEquals("2", getStateVal(err.stateTrace.get(3), "depth"));
        assertEquals("6", getStateVal(err.stateTrace.get(3), "branch"));

        assertEquals("3", getStateVal(err.stateTrace.get(4), "depth"));
        assertEquals("6", getStateVal(err.stateTrace.get(4), "branch"));

        assertEquals("4", getStateVal(err.stateTrace.get(5), "depth"));
        assertEquals("6", getStateVal(err.stateTrace.get(5), "branch"));

        assertEquals("5", getStateVal(err.stateTrace.get(6), "depth"));
        assertEquals("6", getStateVal(err.stateTrace.get(6), "branch"));

        worker.join();
        assertFalse(worker.isAlive());
    }

    @Category(IndependentlyRunTest.class)
    @Test
    public void testModelStateConstraint() throws Exception {
        final ITool tool = new FastTool("", "BasicMultiTrace", "MCWithConstraint", new SimpleFilenameToStream(), Mode.Simulation);

        final StateVec initStates = tool.getInitStates();
        final ILiveCheck liveCheck = new NoOpLiveCheck(tool, "BasicMultiTrace");
        final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();
        final SimulationWorker worker = new SimulationWorker(0, tool, resultQueue, 0, 100, 100, false, null,
                liveCheck);
        worker.start(initStates);
        final SimulationWorkerResult res = resultQueue.take();
        assertFalse(res.isError());
        worker.join();
        assertTrue(resultQueue.isEmpty());
        assertFalse(worker.isAlive());
    }

    @Category(IndependentlyRunTest.class)
    @Test
    public void testModelActionConstraint() throws Exception {
        final ITool tool = new FastTool("", "BasicMultiTrace", "MCWithActionConstraint", new SimpleFilenameToStream(), Mode.Simulation);

        final StateVec initStates = tool.getInitStates();
        final ILiveCheck liveCheck = new NoOpLiveCheck(tool, "BasicMultiTrace");
        final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();
        final SimulationWorker worker = new SimulationWorker(0, tool, resultQueue, 0, 100, 100, false, null,
                liveCheck);
        worker.start(initStates);
        final SimulationWorkerResult res = resultQueue.take();
        assertFalse(res.isError());
        worker.join();
        assertTrue(resultQueue.isEmpty());
        assertFalse(worker.isAlive());
    }

    @Test
    public void testWorkerInterruption() throws Exception {
        final ITool tool = new FastTool("", "BasicMultiTrace", "MCInv", new SimpleFilenameToStream(), Mode.Simulation);

        final StateVec initStates = tool.getInitStates();
        final ILiveCheck liveCheck = new NoOpLiveCheck(tool, "BasicMultiTrace");
        final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();

        // If we set the trace limit to the max, the worker should effectively run forever. We verify that after it generates
        // a result, we can cancel it and the worker will terminate.
        final long traceNum = Long.MAX_VALUE;
        final SimulationWorker worker = new SimulationWorker(0, tool, resultQueue, 0, 100, traceNum, false, null,
                liveCheck);
        worker.start(initStates);

        // Check one result.
        final SimulationWorkerResult res = resultQueue.take();

        assertTrue(res.isError());
        final SimulationWorkerError err = res.error();
        assertEquals(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, err.errorCode);
        assertEquals(3, err.stateTrace.size());

        // Cancel the worker.
        worker.interrupt();
        worker.join();
        assertFalse(worker.isAlive());
    }

    @Test
    public void testTraceDepthObeyed() throws Exception {
        final ITool tool = new FastTool("", "BasicMultiTrace", "MCInv", new SimpleFilenameToStream(), Mode.Simulation);

        final StateVec initStates = tool.getInitStates();
        final ILiveCheck liveCheck = new NoOpLiveCheck(tool, "BasicMultiTrace");
        final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();

        // At this trace depth, the worker should never find the invariant violation.
        final int traceDepth = 1;
        final SimulationWorker worker = new SimulationWorker(0, tool, resultQueue, 0, traceDepth, 100, false,
                null, liveCheck);
        worker.start(initStates);
        final SimulationWorkerResult res = resultQueue.take();
        assertFalse(res.isError());

        worker.join();
        assertTrue(resultQueue.isEmpty());
        assertFalse(worker.isAlive());
    }

    @Test
    public void testStateAndTraceGenerationCount() throws Exception {
        final ITool tool = new FastTool("", "BasicMultiTrace", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME, new SimpleFilenameToStream(), Mode.Simulation);

        final StateVec initStates = tool.getInitStates();
        final ILiveCheck liveCheck = new NoOpLiveCheck(tool, "BasicMultiTrace");
        final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();

        // Have the worker generate a specified number of traces of a fixed length.
        final LongAdder numOfGenStates = new LongAdder();
        final LongAdder numOfGenTraces = new LongAdder();
        final AtomicLong m2AndMean = new AtomicLong();
        final int traceDepth = 5;
        final long traceNum = 5;
        final SimulationWorker worker = new SimulationWorker(0, tool, resultQueue, 0, traceDepth, traceNum, null, false,
                null, liveCheck, numOfGenStates, numOfGenTraces, m2AndMean);

        worker.start(initStates);
        worker.join();
        assertFalse(worker.isAlive());
        assertEquals(70, numOfGenStates.longValue());
        assertEquals(5, numOfGenTraces.longValue());
        // With traces all length 5, mean is 5 and m2 is 0, hence m2AndMean = 5
        assertEquals(5, m2AndMean.get());
    }
}
