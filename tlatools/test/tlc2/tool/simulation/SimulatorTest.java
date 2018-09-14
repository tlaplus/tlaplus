package tlc2.tool.simulation;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.File;

import org.junit.Test;
import org.junit.Before;
import org.junit.After;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.CommonTestCase;
import tlc2.tool.Simulator;
import tlc2.util.RandomGenerator;
import util.FileUtil;
import util.SimpleFilenameToStream;
import util.ToolIO;

/**
 * Correctness tests of single-threaded Simulator.
 */
public class SimulatorTest extends CommonTestCase {
	
	RandomGenerator rng = new RandomGenerator();

	public SimulatorTest() {
		super(new TestMPRecorder());
		MP.setRecorder(recorder);
		TLC.traceNum = 100;
	}
	
	@Before
	public void setUp() throws Exception{
		// Make the each unit test execution as deterministic as possible.
		rng = new RandomGenerator(0);
		ToolIO.setUserDir(BASE_PATH + File.separator + "simulation" + File.separator + "BasicMultiTrace");
	}
	
	@After
	public void tearDown() throws Exception{
        FileUtil.deleteDir(TLCGlobals.metaRoot, true);
	}
	
	/**
	 * The number of threads to run the Simulator with. Can be overridden by
	 * sub-classes that want to test with different values.
	 */
	public int numWorkers() {
		return 1;
	}

	public void runSimulatorTest(String specFile, String configFile, Boolean deadlock, int traceDepth, long traceNum) {
		try {
			Simulator simulator = new Simulator(specFile, configFile, null, deadlock, traceDepth, traceNum, rng, 0,
					true, new SimpleFilenameToStream(), null, numWorkers());
			simulator.simulate();
		} catch (Exception e) {
			fail(e.getMessage());
		}
	}
	
	@Test
	public void testInvariantViolationInitialState() {	
		runSimulatorTest("BasicMultiTrace", "MCInvInitState", false, 100, 100);
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INVARIANT_VIOLATED_INITIAL, "InvInitState"));
	}
	
	@Test
	public void testInvariantViolation() {	
		runSimulatorTest("BasicMultiTrace", "MCInv", false, 100, 100);
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, "Inv"));
	}
	
	@Test
	public void testInvariantBadEvalInitState() {
		runSimulatorTest("BasicMultiTrace", "MCBadInvInitState", false, 100, 100);
		assertTrue(recorder.recorded(EC.TLC_INITIAL_STATE));
	}
	
	@Test
	public void testInvariantBadEvalNonInitState() {
		runSimulatorTest("BasicMultiTrace", "MCBadInvNonInitState", false, 100, 100);
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INVARIANT_EVALUATION_FAILED, "InvBadEvalNonInitState"));
	}
	
	@Test
	public void testUnderspecifiedNext() {
		runSimulatorTest("BasicMultiTrace", "MCUnderspecNext", false, 100, 100);
		assertTrue(recorder.recorded(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT));
	}
	
	@Test
	public void testUnderspecifiedInit() {
		runSimulatorTest("BasicMultiTrace", "MCUnderspecInit", false, 100, 100);
		assertTrue(recorder.recorded(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL));
	}
	
	@Test
	public void testDeadlock() {
		runSimulatorTest("BasicMultiTrace", "MC", true, 100, 100);
		assertTrue(recorder.recorded(EC.TLC_DEADLOCK_REACHED));
	}
	

}
