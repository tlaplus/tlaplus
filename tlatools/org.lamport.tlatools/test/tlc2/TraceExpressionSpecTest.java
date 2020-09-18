package tlc2;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import java.io.ByteArrayOutputStream;
import java.io.FileNotFoundException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.UUID;
import java.util.function.BiFunction;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import classloadhelper.IsolatedTLCRunner;
import util.SubsetHelper;
import util.TLAConstants;
import util.ToolIO;
import tlc2.model.MCError;
import tlc2.model.MCState;
import tlc2.output.ErrorTraceMessagePrinterRecorder;

/**
 * Tests for {@link tlc2.TraceExpressionSpec}, both in isolation and
 * integrated with {@link tlc2.TLC}.
 */
public class TraceExpressionSpecTest {
	
	/**
	 * Whether to print TLC console output while running tests.
	 * Useful to have this flag in one place for debugging test failures.
	 * If you run into a test failure, set this to true to see TLC output.
	 */
	private static final boolean printTLCConsoleOutput = false;
	
	/**
	 * Stores then restores standard output stream.
	 */
	private PrintStream toolOutput = null;
	
	/**
	 * Silences standard output for unit tests.
	 */
	@Before
	public void setup() {
		if (!printTLCConsoleOutput) {
			this.toolOutput = ToolIO.out;
			ToolIO.out = new PrintStream(OutputStream.nullOutputStream());
		}
	}
	
	/**
	 * Restores standard output after unit tests finish.
	 */
	@After
	public void teardown() {
		if (!printTLCConsoleOutput) {
			ToolIO.out = this.toolOutput;
		}
	}
	
	/**
	 * Given a spec generating a simple safety violation error trace, tests
	 * that the generated TE spec results in the same error trace.
	 * Iterates through subsets of possible CL arguments.
	 */
	@Test
	public void integrationTestSafetyViolationTESpec() {
		Set<String> possibleArgs = new HashSet<String>(Arrays.asList(new String[] {
			"-workers 4",
			"-tool"
		}));
		
		for (String[] args : SubsetHelper.toArgsSubsets(SubsetHelper.getSubsetsOf(possibleArgs))) {
			assertTrue(integrationTestSafetyViolation("TESpecTest", "TESpecSafetyTest", args));
			assertTrue(integrationTestSafetyViolationSimulation("TESpecTest", "TESpecSafetyTest", args));
		}
	}

	/**
	 * Given a spec generating a deadlock error trace, tests
	 * that the generated TE spec results in the same error trace.
	 * Iterates through subsets of possible CL arguments.
	 */
	@Test
	public void integrationTestDeadlockViolationTESpec() {
		Set<String> possibleArgs = new HashSet<String>(Arrays.asList(new String[] {
			"-workers 4",
			"-tool"
		}));
		
		for (String[] args : SubsetHelper.toArgsSubsets(SubsetHelper.getSubsetsOf(possibleArgs))) {
			assertTrue(integrationTestSafetyViolation("TESpecDeadlockTest", "TESpecDeadlockTest", args));
			assertTrue(integrationTestSafetyViolationSimulation("TESpecDeadlockTest", "TESpecDeadlockTest", args));
		}
	}
	
	/**
	 * Given a spec where TLC encounters a runtime error during evaluation,
	 * check that TLC generates a TE spec which produces the same trace.
	 */
	@Test
	public void integrationTestTLCRuntimeEvaluationErrorTESpec() {
		assertTrue(integrationTestSafetyViolation("TESpecRuntimeErrorTest", "TESpecRuntimeErrorTest"));
		assertTrue(integrationTestSafetyViolationSimulation("TESpecRuntimeErrorTest", "TESpecRuntimeErrorTest"));
	}
	
	/**
	 * Given a PlusCal spec generating an assert error trace, tests
	 * that the generated TE spec results in the same error trace.
	 * Iterates through subsets of possible CL arguments.
	 */
	@Test
	public void integrationTestPlusCalAssertTESpec() {
		Set<String> possibleArgs = new HashSet<String>(Arrays.asList(new String[] {
			"-workers 4",
			"-tool"
		}));
		
		for (String[] args : SubsetHelper.toArgsSubsets(SubsetHelper.getSubsetsOf(possibleArgs))) {
			assertTrue(integrationTestSafetyViolation("TESpecPlusCalTest", "TESpecPlusCalTest", args));
			assertTrue(integrationTestSafetyViolationSimulation("TESpecPlusCalTest", "TESpecPlusCalTest", args));
		}
	}
	
	/**
	 * Given a spec generating a simple stuttering error trace, tests
	 * that the generated TE spec results in the same error trace.
	 */
	@Test
	public void integrationTestStutteringTESpec() {
		Set<String> possibleArgs = new HashSet<String>(Arrays.asList(new String[] {
			"-tool"
		}));
		
		for (String[] args : SubsetHelper.toArgsSubsets(SubsetHelper.getSubsetsOf(possibleArgs))) {
			assertTrue(integrationTestStutteringLivenessViolation(args));
		}
	}
	
	/**
	 * Given a spec generating a simple lasso error trace, tests
	 * that the generated TE spec results in the same error trace.
	 */
	@Test
	public void integrationTestLassoTESpec() {
		Set<String> possibleArgs = new HashSet<String>(Arrays.asList(new String[] {
			"-tool"
		}));
		
		for (String[] args : SubsetHelper.toArgsSubsets(SubsetHelper.getSubsetsOf(possibleArgs))) {
			assertTrue(integrationTestLassoLivenessViolation(args));
		}
	}
	
	/**
	 * Tests various cases in which a TE spec shouldn't be generated.
	 */
	@Test
	public void integrationTestTESpecNotGenerated() {
		final Path modelDir = Paths.get("test-model", "TESpecTest");
		final Path tempDir = modelDir.resolve("temp");
		final Path teDir = tempDir.resolve(UUID.randomUUID().toString());
		final String teSpecName = TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + TLAConstants.Files.TLA_EXTENSION;
		final Path teSpecPath = teDir.resolve(teSpecName);

		// Tests TE spec not generated with -noGenerateSpecTE flag
		Path tlaPath = modelDir.resolve("TESpecTest" + TLAConstants.Files.TLA_EXTENSION);
		Path cfgPath = modelDir.resolve("TESpecSafetyTest" + TLAConstants.Files.CONFIG_EXTENSION);
		Path stateDir = tempDir.resolve(UUID.randomUUID().toString());
		String[] searchDirs = new String[] { modelDir.toString() };
		String[] args = new String[] {
			"-noGenerateSpecTE",
			"-teSpecOutDir", teDir.toString(),
			"-metadir", stateDir.toString(),
			"-config", cfgPath.toString(),
			tlaPath.toString()
		};
		
		IsolatedTLCRunner tlc = new IsolatedTLCRunner(printTLCConsoleOutput);
		assertTrue(tlc.initialize(searchDirs, args));
		Optional<MCError> ogError = tlc.run();
		assertTrue(ogError.isPresent());
		assertFalse(teSpecPath.toFile().exists());
		
		// Tests TE spec not generated when no invariant violation occurs
		tlaPath = modelDir.resolve("TESpecNoErrorTest" + TLAConstants.Files.TLA_EXTENSION);
		cfgPath = modelDir.resolve("TESpecNoErrorTest" + TLAConstants.Files.CONFIG_EXTENSION);
		stateDir = tempDir.resolve(UUID.randomUUID().toString());
		args = new String[] {
			"-teSpecOutDir", teDir.toString(),
			"-metadir", stateDir.toString(),
			"-config", cfgPath.toString(),
			tlaPath.toString()
		};
		
		tlc = new IsolatedTLCRunner(printTLCConsoleOutput);
		assertTrue(tlc.initialize(searchDirs, args));
		ogError = tlc.run();
		assertFalse(ogError.isPresent());
		assertFalse(teSpecPath.toFile().exists());
	}
	
	/**
	 * Tests that a TE spec is not generated with TLC encounters a runtime
	 * error that is not an invariant violation.
	 */
	@Test
	public void integrationTestTESpecNotGeneratedOnRuntimeError() {
		final Path modelDir = Paths.get("test-model", "TESpecTest");
		final Path tempDir = modelDir.resolve("temp");
		final Path teDir = tempDir.resolve(UUID.randomUUID().toString());
		final String teSpecName = TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + TLAConstants.Files.TLA_EXTENSION;
		final Path teSpecPath = teDir.resolve(teSpecName);

		// Tests error trace not generated when TLA file doesn't exist
		Path tlaPath = modelDir.resolve("DoesNotExist" + TLAConstants.Files.TLA_EXTENSION);
		Path cfgPath = modelDir.resolve("TESpecSafetyTest" + TLAConstants.Files.CONFIG_EXTENSION);
		Path stateDir = tempDir.resolve(UUID.randomUUID().toString());
		String[] searchDirs = new String[] { modelDir.toString() };
		String[] args = new String[] {
			"-teSpecOutDir", teDir.toString(),
			"-metadir", stateDir.toString(),
			"-config", cfgPath.toString(),
			tlaPath.toString()
		};
		
		IsolatedTLCRunner tlc = new IsolatedTLCRunner(printTLCConsoleOutput);
		assertTrue(tlc.initialize(searchDirs, args));
		Optional<MCError> ogError = tlc.run();
		assertFalse(ogError.isPresent());
		assertFalse(teSpecPath.toFile().exists());
		
		// Tests error trace not generated with CFG file doesn't exist
		tlaPath = modelDir.resolve("TESpecTest" + TLAConstants.Files.TLA_EXTENSION);
		cfgPath = modelDir.resolve("DoesNotExist" + TLAConstants.Files.CONFIG_EXTENSION);
		stateDir = tempDir.resolve(UUID.randomUUID().toString());
		args = new String[] {
			"-teSpecOutDir", teDir.toString(),
			"-metadir", stateDir.toString(),
			"-config", cfgPath.toString(),
			tlaPath.toString()
		};
		
		tlc = new IsolatedTLCRunner(printTLCConsoleOutput);
		assertTrue(tlc.initialize(searchDirs, args));
		ogError = tlc.run();
		assertFalse(ogError.isPresent());
		assertFalse(teSpecPath.toFile().exists());
		
		// Tests error trace not generated with module dependency not found
		tlaPath = modelDir.resolve("TESpecDependencyTest" + TLAConstants.Files.TLA_EXTENSION);
		cfgPath = modelDir.resolve("TESpecDependencyTest" + TLAConstants.Files.CONFIG_EXTENSION);
		stateDir = tempDir.resolve(UUID.randomUUID().toString());
		args = new String[] {
			"-teSpecOutDir", teDir.toString(),
			"-metadir", stateDir.toString(),
			"-config", cfgPath.toString(),
			tlaPath.toString()
		};
		
		tlc = new IsolatedTLCRunner(printTLCConsoleOutput);
		assertTrue(tlc.initialize(searchDirs, args));
		ogError = tlc.run();
		assertFalse(ogError.isPresent());
		assertFalse(teSpecPath.toFile().exists());
	}
	
	/**
	 * Tests setting & getting the output directory of the TE generator.
	 */
	@Test
	public void testSetOutputDirectory() {
		Path expected = Paths.get("trace");
		ErrorTraceMessagePrinterRecorder recorder = new FakeErrorRecorder(null);
		TraceExpressionSpec teSpec = new TraceExpressionSpec(expected, recorder);
		assertEquals(expected, teSpec.getOutputDirectory());
	}
	
	/**
	 * Tests TE generation code handles exceptions correctly.
	 */
	@Test
	public void testFileWriteExceptions() {
		ErrorTraceMessagePrinterRecorder recorder = new FakeErrorRecorder(null);

		FakeStreamProvider stream = new FakeStreamProvider(null, null, ThrowException.TLA_FILENOTFOUND);
		TraceExpressionSpec teSpec = new TraceExpressionSpec(stream, recorder);
		assertFalse(teSpec.generate(null, null, null, null));

		stream = new FakeStreamProvider(null, null, ThrowException.TLA_SECURITY);
		teSpec = new TraceExpressionSpec(stream, recorder);
		assertFalse(teSpec.generate(null, null, null, null));

		stream = new FakeStreamProvider(null, null, ThrowException.CFG_FILENOTFOUND);
		teSpec = new TraceExpressionSpec(stream, recorder);
		assertFalse(teSpec.generate(null, null, null, null));

		stream = new FakeStreamProvider(null, null, ThrowException.CFG_SECURITY);
		teSpec = new TraceExpressionSpec(stream, recorder);
		assertFalse(teSpec.generate(null, null, null, null));
	}
	
	/**
	 * Given a spec generating a simple safety violation error trace, tests
	 * that the generated TE spec results in the same error trace.
	 * @param args Additional arguments to pass to TLC.
	 * @return Whether execution was successful.
	 */
	public static boolean integrationTestSafetyViolation(String tla, String cfg, String... args) {
		BiFunction<MCError, MCError, Boolean> eval = (originalError, teError) -> {
			List<MCState> originalStates = originalError.getStates();
			List<MCState> teStates = teError.getStates();
			assertEquals(originalStates.size(), teStates.size());
			for (int i = 0; i < originalStates.size(); i++)
			{
				MCState originalState = originalStates.get(i);
				MCState teState = teStates.get(i);

				assertEquals(i + 1, originalState.getStateNumber());
				assertEquals(originalState.getStateNumber(), teState.getStateNumber());

				assertFalse(originalState.isBackToState());
				assertEquals(originalState.isBackToState(), teState.isBackToState());
				
				assertFalse(originalState.isStuttering());
				assertEquals(originalState.isStuttering(), teState.isStuttering());
				
				assertEquals(originalState.asSimpleRecord(), teState.asSimpleRecord());
			}
			
			return true;
		};

		assertTrue(teSpecTest(tla, cfg, eval, args));
		
		return true;
	}
	
	/**
	 * Given a spec generating a simple safety violation error trace, tests
	 * that the generated TE spec results in the same error trace.
	 * Runs TLC in simulation mode.
	 */
	public boolean integrationTestSafetyViolationSimulation(String tla, String cfg, String... args) {
		BiFunction<MCError, MCError, Boolean> eval = (originalError, teError) -> {
			List<MCState> originalStates = originalError.getStates();
			List<MCState> teStates = teError.getStates();
			
			// Since simulation trace doesn't have to be most direct path to
			// counterexample state, can only compare first & last states
			// since TE trace will be shortest path.
			assertTrue(originalStates.size() >= teStates.size());
			
			MCState ogInitState = originalStates.get(0);
			MCState teInitState = teStates.get(0);
			assertEquals(1, ogInitState.getStateNumber());
			assertEquals(ogInitState.getStateNumber(), teInitState.getStateNumber());
			assertFalse(ogInitState.isBackToState());
			assertEquals(ogInitState.isBackToState(), teInitState.isBackToState());
			assertFalse(ogInitState.isStuttering());
			assertEquals(ogInitState.isStuttering(), teInitState.isStuttering());
			assertEquals(ogInitState.asSimpleRecord(), teInitState.asSimpleRecord());

			MCState ogFinalState = originalStates.get(originalStates.size() - 1);
			MCState teFinalState = teStates.get(teStates.size() - 1);
			assertFalse(ogFinalState.isBackToState());
			assertEquals(ogFinalState.isBackToState(), teFinalState.isBackToState());
			assertFalse(ogFinalState.isStuttering());
			assertEquals(ogFinalState.isStuttering(), teFinalState.isStuttering());
			assertEquals(ogFinalState.asSimpleRecord(), teFinalState.asSimpleRecord());

			return true;
		};

		return teSpecTest(tla, cfg, eval, append(args, "-simulate"));
	}
	
	/**
	 * Given a spec generating a stuttering liveness violation error trace,
	 * tests that the generated TE spec results in the same error trace.
	 * @param args Additional arguments to pass to TLC.
	 * @return Whether execution was successful.
	 */
	public boolean integrationTestStutteringLivenessViolation(String... args) {
		BiFunction<MCError, MCError, Boolean> eval = (originalError, teError) -> {
			List<MCState> originalStates = originalError.getStates();
			List<MCState> teStates = teError.getStates();
			assertEquals(originalStates.size(), teStates.size());
			for (int i = 0; i < originalStates.size(); i++)
			{
				MCState originalState = originalStates.get(i);
				MCState teState = teStates.get(i);

				assertFalse(originalState.isBackToState());
				assertEquals(originalState.isBackToState(), teState.isBackToState());
				
				if (originalStates.size() == i + 1) {
					assertEquals(i, originalState.getStateNumber());
					assertEquals(originalState.getStateNumber(), teState.getStateNumber());
					assertTrue(originalState.isStuttering());
					assertEquals(originalState.isStuttering(), teState.isStuttering());
				} else {
					assertEquals(i + 1, originalState.getStateNumber());
					assertEquals(originalState.getStateNumber(), teState.getStateNumber());
					assertFalse(originalState.isStuttering());
					assertEquals(originalState.isStuttering(), teState.isStuttering());
				}
				
				assertEquals(originalState.asSimpleRecord(), teState.asSimpleRecord());
			}
			
			return true;
		};

		return teSpecTest("TESpecTest", "TESpecStutteringTest", eval);
	}
	
	/**
	 * Given a spec generating a simple lasso liveness violation error trace,
	 * tests that the generated TE spec results in the same error trace.
	 * @param args Additional arguments to pass to TLC.
	 * @return Whether execution was successful.
	 */
	public boolean integrationTestLassoLivenessViolation(String... args) {
		BiFunction<MCError, MCError, Boolean> eval = (originalError, teError) -> {
			List<MCState> originalStates = originalError.getStates();
			List<MCState> teStates = teError.getStates();
			assertEquals(originalStates.size(), teStates.size());
			for (int i = 0; i < originalStates.size(); i++)
			{
				MCState originalState = originalStates.get(i);
				MCState teState = teStates.get(i);
				
				assertFalse(originalState.isStuttering());
				assertEquals(originalState.isStuttering(), teState.isStuttering());

				if (originalStates.size() == i + 1) {
					assertTrue(1 <= originalState.getStateNumber());
					assertTrue(originalState.getStateNumber() < i);
					assertEquals(originalState.getStateNumber(), teState.getStateNumber());
					assertTrue(originalState.isBackToState());
					assertEquals(originalState.isBackToState(), teState.isBackToState());
				} else {
					assertEquals(i + 1, originalState.getStateNumber());
					assertEquals(originalState.getStateNumber(), teState.getStateNumber());
					assertFalse(originalState.isBackToState());
					assertEquals(originalState.isBackToState(), teState.isBackToState());
				}
				
				assertEquals(originalState.asSimpleRecord(), teState.asSimpleRecord());
			}
			
			return true;
		};
		
		return teSpecTest("TESpecTest", "TESpecLassoTest", eval, args);
	}

	/**
	 * Runs TLC on a spec, runs TLC on the resulting TE spec, then compares
	 * the two error traces.
	 * @param cfgName Name of the TLA+ config file.
	 * @param eval Function comparing the two error traces.
	 * @param otherArgs Additional arguments for TLC.
	 * @return Whether all operations were successful.
	 */
	public static boolean teSpecTest(String tlaName, String cfgName, BiFunction<MCError, MCError, Boolean> eval, String... otherArgs) {
		// Defines various directories & paths
		final Path modelDir = Paths.get("test-model", "TESpecTest");
		final Path tempDir = modelDir.resolve("temp");
		final Path ogStateDir = tempDir.resolve(UUID.randomUUID().toString());
		final Path teDir = tempDir.resolve(UUID.randomUUID().toString());
		final Path ogTlaPath = modelDir.resolve(tlaName + TLAConstants.Files.TLA_EXTENSION);
		final Path ogCfgPath = modelDir.resolve(cfgName + TLAConstants.Files.CONFIG_EXTENSION);
		final String teSpecName = TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + TLAConstants.Files.TLA_EXTENSION;

		// Better error reporting for https://github.com/tlaplus/tlaplus/issues/545
		// Remove below when issue #545 is fixed
		Path zombieTeSpec = modelDir.resolve(teSpecName);
		assertFalse("Zombie TE spec exists at " + zombieTeSpec.toString(), zombieTeSpec.toFile().exists());
		zombieTeSpec = Paths.get(".", teSpecName);
		assertFalse("Zombie TE spec exists at " + zombieTeSpec.toString(), zombieTeSpec.toFile().exists());
		// Remove above when issue #545 is fixed
		
		// First run of TLC to generate error trace & TE spec
		String[] searchDirs = new String[] { modelDir.toString() };
		String[] baseArgs = new String[] {
			"-teSpecOutDir", teDir.toString(),
			"-metadir", ogStateDir.toString(),
			"-config", ogCfgPath.toString(),
		};
		
		String[] args = append(concat(baseArgs, otherArgs), ogTlaPath.toString());

		if (printTLCConsoleOutput) {
			System.out.println(Arrays.asList(args));
		}

		IsolatedTLCRunner tlc = new IsolatedTLCRunner(printTLCConsoleOutput);
		assertTrue(tlc.initialize(searchDirs, args));
		Optional<MCError> ogError = tlc.run();
		assertTrue(Arrays.asList(args).toString(), ogError.isPresent());

		// Second run of TLC to run TE spec
		final Path teStateDir = tempDir.resolve(UUID.randomUUID().toString());
		final Path teTlaPath = teDir.resolve(teSpecName);
		
		searchDirs = new String[] { modelDir.toString(), teDir.toString() };
		args = new String[] { "-metadir", teStateDir.toString(), teTlaPath.toString() };

		tlc = new IsolatedTLCRunner(printTLCConsoleOutput);
		assertTrue(tlc.initialize(searchDirs, args));
		Optional<MCError> teError = tlc.run();
		assertTrue(teError.isPresent());

		// Tests equivalence of original error trace with TE error trace
		return eval.apply(ogError.get(), teError.get());
	}

	/**
	 * Helper class to inject IO exceptions into the TE generation code.
	 */
	private class FakeStreamProvider implements TraceExpressionSpec.IStreamProvider {
		
		private ByteArrayOutputStream tlaStream;
		
		private ByteArrayOutputStream cfgStream;
		
		private ThrowException ex;
		
		public FakeStreamProvider(
				ByteArrayOutputStream tlaStream,
				ByteArrayOutputStream cfgStream,
				ThrowException ex) {
			this.tlaStream = tlaStream;
			this.cfgStream = cfgStream;
			this.ex = ex;
		}

		@Override
		public OutputStream getTlaStream() throws FileNotFoundException, SecurityException {
			switch (this.ex) {
				case TLA_SECURITY:
					throw new SecurityException("TLA_SECURITY");
				case TLA_FILENOTFOUND:
					throw new FileNotFoundException("TLA_FILENOTFOUND");
				default:
					return this.tlaStream;
			}
		}

		@Override
		public OutputStream getCfgStream() throws FileNotFoundException, SecurityException {
			switch (this.ex) {
				case CFG_SECURITY:
					throw new SecurityException("CFG_SECURITY");
				case CFG_FILENOTFOUND:
					throw new FileNotFoundException("CFG_FILENOTFOUND");
				default:
					return this.cfgStream;
			}
		}
	}
	
	
	/**
	 * Concatenates two arrays.
	 * @param a First array.
	 * @param b Second array.
	 * @return Concatenated arrays.
	 */
	private static String[] concat(String[] a, String[] b) {
		String[] c = new String[a.length + b.length];
		for (int i = 0; i < a.length; i++) { c[i] = a[i]; }
		for (int i = 0; i < b.length; i++) { c[a.length + i] = b[i]; }
		return c;
	}
	
	/**
	 * Appends an element to an array.
	 * @param a Array.
	 * @param e Element to append.
	 * @return Array with element appended.
	 */
	private static String[] append(String[] a, String e) {
		String[] b = new String[a.length + 1];
		for (int i = 0; i < a.length; i++) { b[i] = a[i]; }
		b[b.length - 1] = e;
		return b;
	}
	
	private enum ThrowException {
		NONE,
		TLA_SECURITY,
		TLA_FILENOTFOUND,
		CFG_SECURITY,
		CFG_FILENOTFOUND
	}
	
	private class FakeErrorRecorder extends ErrorTraceMessagePrinterRecorder {
		
		private Optional<MCError> trace;
		
		public FakeErrorRecorder(MCError trace)
		{
			this.trace = Optional.ofNullable(trace);
		}
		
		@Override
		public Optional<MCError> getMCErrorTrace() {
			return this.trace;
		}
	}
}
