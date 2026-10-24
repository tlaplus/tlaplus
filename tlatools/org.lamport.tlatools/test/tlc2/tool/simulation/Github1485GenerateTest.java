package tlc2.tool.simulation;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Suite;
import org.junit.runners.Suite.SuiteClasses;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.tool.SimulationWorker;
import tlc2.tool.Simulator;
import tlc2.tool.StateVec;
import tlc2.tool.liveness.ModelCheckerTestCase;

/** Regression tests for the -generate command-line path of issue #1485. */
@RunWith(Suite.class)
@SuiteClasses({ Github1485GenerateTest.AllSuccessors.class, Github1485GenerateTest.Case.class,
		Github1485GenerateTest.RLChosenAction.class, Github1485GenerateTest.RLActionChosenAction.class,
		Github1485GenerateTest.RLHighFanout.class, Github1485GenerateTest.RLActionHighFanout.class,
		Github1485GenerateTest.RLEnabledOnly.class, Github1485GenerateTest.RLActionEnabledOnly.class })
public class Github1485GenerateTest {

	public abstract static class GenerateTestCase extends ModelCheckerTestCase {
		private final boolean enabledOnly;
		private final int minStates;
		private final int maxStates;
		private final Map<String, String> properties = new HashMap<>();

		protected GenerateTestCase(final String spec, final String options, final boolean enabledOnly,
				final int minStates, final int maxStates) {
			super(spec, "/simulation/Github1485", new String[] { "-generate", options, "-depth", "1" });
			this.enabledOnly = enabledOnly;
			this.minStates = minStates;
			this.maxStates = maxStates;
		}

		@Override
		protected void beforeSetUp() {
			// Properties outlive the test runner's class-loader isolation.
			for (final String key : new String[] { SimulationWorker.PROBABILISTIC_KEY,
					"tlc2.tool.Simulator.rl", "tlc2.tool.Simulator.rlaction", "tlc2.tool.Simulator.rl.enabledOnly" }) {
				properties.put(key, System.getProperty(key));
				System.clearProperty(key);
			}
			System.setProperty("tlc2.tool.Simulator.rl.enabledOnly", Boolean.toString(enabledOnly));
		}

		@Override
		protected void beforeTearDown() {
			properties.forEach((key, value) -> {
				if (value == null) {
					System.clearProperty(key);
				} else {
					System.setProperty(key, value);
				}
			});
		}

		@Override
		protected boolean runWithDebugger() {
			return false;
		}

		@Override
		protected boolean noGenerateSpec() {
			return true;
		}

		@Override
		protected boolean doCoverage() {
			return false;
		}

		@Override
		protected boolean doDumpTrace() {
			return false;
		}

		@Test
		public void testSpec() {
			assertTrue(recorder.recorded(EC.TLC_FINISHED));
			assertFalse(recorder.recorded(EC.GENERAL));
			final int states = recorder.getRecordAsInt(EC.TLC_STATS_SIMU);
			assertTrue("Unexpected generated state count: " + states, states >= minStates && states <= maxStates);
			final List<?> workers = (List<?>) getField(Simulator.class, "workers", TLCGlobals.simulator);
			for (final Object worker : workers) {
				final StateVec successors = (StateVec) getField(SimulationWorker.class, "nextStates", worker);
				assertEquals("Only the sampled successor should be retained", 1, successors.size());
			}
		}
	}

	public static class AllSuccessors extends GenerateTestCase {
		public AllSuccessors() {
			super("Github1485Disj", "num=200", false, 1001, 1001);
		}
	}

	public static class Case extends GenerateTestCase {
		public Case() {
			super("Github1485Case", "num=200", false, 201, 201);
		}
	}

	public static class RLChosenAction extends GenerateTestCase {
		public RLChosenAction() {
			super("Github1485Disj", "num=200,sched=rl", false, 201, 801);
		}
	}

	public static class RLActionChosenAction extends GenerateTestCase {
		public RLActionChosenAction() {
			super("Github1485Disj", "num=200,sched=rlaction", false, 201, 801);
		}
	}

	public static class RLHighFanout extends GenerateTestCase {
		public RLHighFanout() {
			super("Github1485HighFanout", "num=1,sched=rl", false, 1000001, 1000001);
		}
	}

	public static class RLActionHighFanout extends GenerateTestCase {
		public RLActionHighFanout() {
			super("Github1485HighFanout", "num=1,sched=rlaction", false, 1000001, 1000001);
		}
	}

	public static class RLEnabledOnly extends GenerateTestCase {
		public RLEnabledOnly() {
			super("Github1485HighFanout", "num=1,sched=rl", true, 1000001, 1000001);
		}
	}

	public static class RLActionEnabledOnly extends GenerateTestCase {
		public RLActionEnabledOnly() {
			super("Github1485HighFanout", "num=1,sched=rlaction", true, 1000001, 1000001);
		}
	}
}
