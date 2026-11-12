package tlc2.tool;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.File;

import org.junit.Before;
import org.junit.Test;

import tlc2.util.FP64;
import tlc2.util.RandomGenerator;
import util.SimpleFilenameToStream;
import util.TLAConstants;
import util.ToolIO;

/**
 * Regression test for multi-worker trace length statistics.
 *
 * Runs simulation with multiple workers at a fixed trace depth and verifies
 * that {@link Simulator#computeAggregateTraceStats()} produces the expected
 * mean and variance via Welford's parallel/partitioned algorithm.
 *
 * With a fixed depth and no invariant violations, every trace hits the depth
 * limit, so the expected mean equals the depth and the expected variance is
 * zero.
 */
public class SimulatorTraceStatsTest {

	private static final String BASE_DIR = System.getProperty("basedir",
			System.getProperty("user.dir", "."));
	private static final String TEST_MODEL = "test-model" + File.separator;
	private static final String BASE_PATH = System.getProperty("basepath",
			BASE_DIR + File.separator + TEST_MODEL);

	private RandomGenerator rng;

	@Before
	public void setUp() throws Exception {
		rng = new RandomGenerator(0);
		ToolIO.setUserDir(BASE_PATH + File.separator + "simulation"
				+ File.separator + "BasicMultiTrace");
		FP64.Init();
	}

	@Test
	public void testMultiWorkerTraceStats() {
		final int numWorkers = 4;
		final int traceDepth = 5;
		final long traceNum = 50;

		try {
			final Simulator simulator = new Simulator("BasicMultiTrace",
					TLAConstants.Files.MODEL_CHECK_FILE_BASENAME, null, false,
					traceDepth, traceNum, rng, 0,
					new SimpleFilenameToStream(), numWorkers);
			simulator.simulate();

			// After simulation, verify the aggregated trace statistics.
			final double[] stats = simulator.computeAggregateTraceStats();
			final double aggMean = stats[0];
			final double aggM2 = stats[1];
			final long aggN = (long) stats[2];

			// Each worker generates traceNum traces, all of length traceDepth.
			assertEquals("aggregate N", numWorkers * traceNum, aggN);
			assertEquals("aggregate mean", traceDepth, aggMean, 0.001);
			// All traces have the same length, so M2 (and variance) must be zero.
			assertEquals("aggregate M2", 0.0, aggM2, 0.001);

		} catch (Exception e) {
			e.printStackTrace();
			fail(e.getMessage());
		}
	}

	@Test
	public void testSingleWorkerTraceStats() {
		final int numWorkers = 1;
		final int traceDepth = 5;
		final long traceNum = 50;

		try {
			final Simulator simulator = new Simulator("BasicMultiTrace",
					TLAConstants.Files.MODEL_CHECK_FILE_BASENAME, null, false,
					traceDepth, traceNum, rng, 0,
					new SimpleFilenameToStream(), numWorkers);
			simulator.simulate();

			final double[] stats = simulator.computeAggregateTraceStats();
			final double aggMean = stats[0];
			final double aggM2 = stats[1];
			final long aggN = (long) stats[2];

			assertEquals("aggregate N", traceNum, aggN);
			assertEquals("aggregate mean", traceDepth, aggMean, 0.001);
			assertEquals("aggregate M2", 0.0, aggM2, 0.001);

		} catch (Exception e) {
			e.printStackTrace();
			fail(e.getMessage());
		}
	}
}
