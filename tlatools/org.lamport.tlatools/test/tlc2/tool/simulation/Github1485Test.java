package tlc2.tool.simulation;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;

import org.junit.Before;
import org.junit.Test;

import tlc2.TestMPRecorder;
import tlc2.output.MP;
import tlc2.tool.CommonTestCase;
import tlc2.tool.ITool;
import tlc2.tool.SimulationWorker;
import tlc2.tool.SimulationWorker.SimulationWorkerResult;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.tool.impl.Tool.Mode;
import tlc2.tool.liveness.ILiveCheck;
import tlc2.tool.liveness.NoOpLiveCheck;
import tlc2.value.impl.IntValue;
import util.SimpleFilenameToStream;
import util.ToolIO;
import util.UniqueString;

/**
 * Regression tests for https://github.com/tlaplus/tlaplus/issues/1485.
 *
 * TLC's -generate mode used to return the first successor state found while
 * trying the actions, disjuncts, and \E bindings of the next-state relation in
 * a pseudo-random (non-uniformly distributed) order.  Consequently, the
 * distribution over successor states was biased in a way that depends on how
 * the spec is written: semantically equivalent next-state relations such as
 * Next and Next /\ TRUE yielded different distributions.
 *
 * These tests simulate the specs in test-model/simulation/Github1485 with a
 * trace length of one and check the frequency of the successor states in the
 * final states of the generated behaviors.  A worker subclass forces uniform
 * successor selection (the behavior of -generate) because the probabilistic
 * system property cannot be flipped for an already loaded SimulationWorker
 * class in the test JVM.
 */
public class Github1485Test extends CommonTestCase {

	private static final int TRACES = 10000;
	private static final long SEED = 42L;

	private static final UniqueString X = UniqueString.uniqueStringOf("x");

	public Github1485Test() {
		super(new TestMPRecorder());
		MP.setRecorder(recorder);
	}

	@Before
	public void setUp() {
		ToolIO.setUserDir(BASE_PATH + File.separator + "simulation" + File.separator + "Github1485");
	}

	/**
	 * A SimulationWorker that forces uniform successor selection (see
	 * SimulationWorker#isUniformSuccessorSelection) and records the value of
	 * variable x in the final state of every generated behavior.
	 */
	private static final class RecordingSimulationWorker extends SimulationWorker {

		private final List<Integer> outcomes = Collections.synchronizedList(new ArrayList<>());
		private final boolean uniform;

		RecordingSimulationWorker(final ITool tool, final BlockingQueue<SimulationWorkerResult> resultQueue,
				final long seed, final int maxTraceDepth, final long maxTraceNum, final ILiveCheck liveCheck,
				final boolean uniform) {
			super(0, tool, resultQueue, seed, maxTraceDepth, maxTraceNum, false, null, liveCheck);
			this.uniform = uniform;
		}

		@Override
		protected boolean isUniformSuccessorSelection() {
			return this.uniform;
		}

		@Override
		protected boolean postTrace(final TLCState finalState) {
			synchronized (this.outcomes) {
				this.outcomes.add(((IntValue) finalState.getVals().get(X)).val);
			}
			return true;
		}
	}

	private List<Integer> simulate(final String spec, final boolean uniform, final long seed, final int traces)
			throws Exception {
		final Tool tool = new FastTool("", spec, spec, new SimpleFilenameToStream(), Mode.Simulation);
		final ILiveCheck liveCheck = new NoOpLiveCheck(tool, spec);
		final StateVec initStates = tool.getInitStates();
		assertEquals(1, initStates.size());

		final BlockingQueue<SimulationWorkerResult> resultQueue = new LinkedBlockingQueue<>();
		final RecordingSimulationWorker worker = new RecordingSimulationWorker(tool, resultQueue, seed, /* depth */ 1,
				traces, liveCheck, uniform);
		worker.start(initStates);
		// The worker pushes a single OK result once it generated `traces` behaviors.
		final SimulationWorkerResult res = resultQueue.take();
		assertTrue(!res.isError());
		worker.join();

		assertEquals(traces, worker.outcomes.size());
		return worker.outcomes;
	}

	private static void assertFrequency(final String message, final List<Integer> outcomes, final int value,
			final double expected, final double tolerance) {
		long cnt = 0;
		synchronized (outcomes) {
			for (final int outcome : outcomes) {
				if (outcome == value) {
					cnt++;
				}
			}
		}
		final double frequency = (double) cnt / outcomes.size();
		final String failure = String.format("%s: Expected frequency of x = %d to be %.3f +/- %.3f but was %.3f (%d/%d)",
				message, value, expected, tolerance, frequency, cnt, outcomes.size());
		assertTrue(failure, Math.abs(frequency - expected) <= tolerance);
	}

	@Test
	public void testDisjunctionOfActions() throws Exception {
		// The actions A (successor states x' \in 0..3 through the bindings of \E i
		// \in 0..3) and B (successor state x' = 4) are both enabled: each of the
		// five successor states has to be selected with probability 1/5.
		final List<Integer> outcomes = simulate("Github1485Disj", true, SEED, TRACES);
		for (int i = 0; i <= 4; i++) {
			assertFrequency("Github1485Disj", outcomes, i, 1d / 5d, 0.04d);
		}
	}

	@Test
	public void testDisjunctionUnderConjunction() throws Exception {
		// Same as testDisjunctionOfActions but with a next-state relation that TLC
		// cannot split into the sub-actions A and B.
		final List<Integer> outcomes = simulate("Github1485ConjTRUE", true, SEED, TRACES);
		for (int i = 0; i <= 4; i++) {
			assertFrequency("Github1485ConjTRUE", outcomes, i, 1d / 5d, 0.04d);
		}
	}

	@Test
	public void testBoundedExists() throws Exception {
		// Bindings 0 and 1 of \E i \in {0, 1, 2} are enabled: both of their
		// successor states have to be selected with probability 1/2.
		final List<Integer> outcomes = simulate("Github1485BoundedExists", true, SEED, TRACES);
		assertFrequency("Github1485BoundedExists", outcomes, 0, 1d / 2d, 0.05d);
		assertFrequency("Github1485BoundedExists", outcomes, 1, 1d / 2d, 0.05d);
	}

	@Test
	public void testSemanticEquivalence() throws Exception {
		// Github1485Disj and Github1485ConjTRUE are semantically equivalent
		// next-state relations that merely differ syntactically.  With uniform
		// successor selection, they induce the same distribution (each successor
		// state 1/5), whereas the previous first-found selection yielded different,
		// spec-shape-dependent distributions.
		final List<Integer> disj = simulate("Github1485Disj", true, SEED, TRACES);
		final List<Integer> conj = simulate("Github1485ConjTRUE", true, SEED, TRACES);
		for (int i = 0; i <= 4; i++) {
			assertFrequency("Github1485Disj", disj, i, 1d / 5d, 0.04d);
			assertFrequency("Github1485ConjTRUE", conj, i, 1d / 5d, 0.04d);
		}
	}

	@Test
	public void testLegacyFirstFoundSelection() throws Exception {
		// With uniform successor selection turned off - the behavior of -simulate
		// and of -generate prior to the fix for issue 1485 - the first of the two
		// actions that generates successor states is selected with probability
		// 1/2.  If A comes first, one of its four successor states is selected at
		// random; if B comes first, its single successor state x = 4 is selected:
		// P(x = i) = 1/8 for i \in 0..3 and P(x = 4) = 1/2.  This test documents
		// the first-found semantics; it fails if -simulate selection semantics
		// change.
		final List<Integer> outcomes = simulate("Github1485Disj", false, SEED, TRACES);
		for (int i = 0; i <= 3; i++) {
			assertFrequency("legacy selection", outcomes, i, 1d / 8d, 0.03d);
		}
		assertFrequency("legacy selection", outcomes, 4, 1d / 2d, 0.03d);
	}
}
