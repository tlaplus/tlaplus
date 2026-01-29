/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.lang.reflect.Method;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import javax.management.MBeanServer;
import javax.management.ObjectName;

import org.junit.After;
import org.junit.Ignore;
import org.junit.Test;

import tlc2.output.EC;
import util.FileUtil;

/**
 * Test case that runs TLC twice using isolated class loaders to test -dumpTrace
 * and -loadTrace functionality. Each TLC run gets its own isolated class
 * loader, ensuring complete isolation of static state (similar to running in
 * separate JVMs but more efficient).
 */
public class DumpLoadTraceTest extends CommonTestCase {

	/**
	 * Isolated class loader for TLC that reloads all TLC-related classes to ensure
	 * static state isolation between test runs. Based on
	 * IsolatedTestCaseRunner.IsolatedTestCaseClassLoader.
	 */
	private static class DumpLoadIsolatedClassLoader extends URLClassLoader {

		private final java.util.Map<String, Class<?>> cache = new java.util.HashMap<>();
		private final java.util.Set<String> packages = new java.util.HashSet<>();

		public DumpLoadIsolatedClassLoader(java.net.URL[] urls, ClassLoader parent) {
			super(urls, parent);

			// All of TLC's java packages that need isolation
			packages.add("tla2sany");
			packages.add("pcal");
			packages.add("util");
			packages.add("tla2tex");
			packages.add("tlc2");
		}

		@Override
		public Class<?> loadClass(String name) throws ClassNotFoundException {
			// Check if we've already loaded this class in this loader instance
			synchronized (getClassLoadingLock(name)) {
				Class<?> c = findLoadedClass(name);
				if (c != null) {
					return c;
				}

				// Check cache
				if (cache.containsKey(name)) {
					return cache.get(name);
				}

				// For classes in our isolated packages, load them ourselves
				for (final String pkg : packages) {
					if (name.startsWith(pkg)) {
						try {
							c = findClass(name);
							cache.put(name, c);
							return c;
						} catch (LinkageError e) {
							// If we get a LinkageError, the class might already be loaded by parent
							// Fall back to parent delegation
							break;
						}
					}
				}

				// Delegate to parent for all other classes
				return super.loadClass(name);
			}
		}
	}

	/**
	 * Container for TLC execution results including the exit code and access to the
	 * recorder for analyzing TLC's output.
	 */
	private static class TLCResult {
		final int exitCode;
		private final Class<?> recorderClass;
		private final Object recorderInstance;

		TLCResult(int exitCode, Object recorderInstance, Class<?> recorderClass) {
			this.exitCode = exitCode;
			this.recorderInstance = recorderInstance;
			this.recorderClass = recorderClass;
		}

		/**
		 * Get the list of records for a specific error code.
		 *
		 * @param ec The error code
		 * @return List of recorded objects (as Object to avoid class loader issues)
		 */
		@SuppressWarnings("unchecked")
		List<Object> getRecords(int ec) {
			try {
				Method getRecords = recorderClass.getMethod("getRecords", int.class);
				return (List<Object>) getRecords.invoke(recorderInstance, ec);
			} catch (Exception e) {
				throw new RuntimeException("Failed to get records for EC: " + ec, e);
			}
		}

		/**
		 * Get TLC statistics as strings: [states generated, distinct states, states on
		 * queue]
		 */
		String[] getStatsAsStrings() {
			try {
				List<Object> stats = getRecords(EC.TLC_STATS);
				if (stats == null || stats.isEmpty()) {
					return new String[] { "0", "0", "0" };
				}
				// Stats are recorded as String[]
				return (String[]) stats.get(0);
			} catch (Exception e) {
				throw new RuntimeException("Failed to get TLC_STATS", e);
			}
		}

		/**
		 * Check if the recorder recorded a specific error code.
		 *
		 * @param ec The error code to check (from the non-isolated EC class)
		 * @return true if the error code was recorded
		 */
		boolean recordedEC(int ec) {
			try {
				Method recorded = recorderClass.getMethod("recorded", int.class);
				return (Boolean) recorded.invoke(recorderInstance, ec);
			} catch (Exception e) {
				throw new RuntimeException("Failed to check recorded EC: " + ec, e);
			}
		}
	}

	private File tempDir;

	/**
	 * Compare two error traces to ensure they represent the same counterexample.
	 */
	private void assertTracesEqual(List<Object> trace1, List<Object> trace2) throws Exception {
		assertEquals("Traces must have same length", trace1.size(), trace2.size());

		for (int i = 0; i < trace1.size(); i++) {
			Object[] state1 = (Object[]) trace1.get(i);
			Object[] state2 = (Object[]) trace2.get(i);

			// state[0] is TLCStateInfo, state[1] is the state number
			assertEquals("State numbers should match at position " + i, state1[1], state2[1]);

			// Compare state strings
			String stateStr1 = state1[0].toString().trim();
			String stateStr2 = state2[0].toString().trim();
			assertEquals("States should be identical at position " + i, stateStr1, stateStr2);
		}
	}

	/**
	 * Verify that trace2 is a prefix of (or equal to) trace1. This is used when
	 * comparing traces from runs with different worker counts, where the single
	 * worker run may find a shorter counterexample.
	 */
	private void assertTraceIsPrefix(List<Object> longerTrace, List<Object> prefixTrace) throws Exception {
		assertTrue("Prefix trace must not be empty", prefixTrace.size() > 0);
		assertTrue(String.format("Prefix trace length (%d) should not exceed longer trace length (%d)",
				prefixTrace.size(), longerTrace.size()), prefixTrace.size() <= longerTrace.size());

		// Verify each state in the prefix matches the corresponding state in the longer
		// trace
		for (int i = 0; i < prefixTrace.size(); i++) {
			Object[] state1 = (Object[]) longerTrace.get(i);
			Object[] state2 = (Object[]) prefixTrace.get(i);

			// state[0] is TLCStateInfo, state[1] is the state number
			assertEquals("State numbers should match at position " + i, state1[1], state2[1]);

			// Compare state strings
			String stateStr1 = state1[0].toString().trim();
			String stateStr2 = state2[0].toString().trim();
			assertEquals("States should be identical at position " + i, stateStr1, stateStr2);
		}
	}

	/**
	 * Builds the command-line arguments for running TLC.
	 * <p>
	 * Note: The working directory is set via ToolIO.setUserDir() in
	 * runTLCInIsolation, not through command-line arguments.
	 * </p>
	 * <p>
	 * The fingerprint determines the ordering of TLC states—for example, in
	 * collections of successor states—and therefore influences both the shape of
	 * the state graph and the order of the BFS search. For -loadTrace to work
	 * reliably, TLC must be run with the same fingerprint that was used when the
	 * trace was created, in order to guarantee an identical state graph. Ensuring
	 * this consistency is the user's responsibility, although some
	 * dumptrace/loadtrace formats may emit a warning if a mismatch is detected.
	 * </p>
	 */
	private String[] buildArgs(String metaDir, String specFile, int fingerprint, String workers, String[] extraArgs,
			String... traceArgs) {
		List<String> args = new ArrayList<>();

		args.add("-metadir");
		args.add(metaDir);
		args.add("-workers");
		args.add(workers);
		args.add("-noGenerateSpecTE");
		args.add("-fp");
		args.add(String.valueOf(fingerprint));

		// Add extra args (like -deadlock, -config)
		for (String arg : extraArgs) {
			args.add(arg);
		}

		// Add trace args (-dumpTrace/-loadTrace format file)
		for (String arg : traceArgs) {
			args.add(arg);
		}

		args.add(specFile);

		return args.toArray(new String[0]);
	}

	@After
	public void cleanup() throws Exception {
		if (tempDir != null && tempDir.exists()) {
			FileUtil.deleteDir(tempDir, true);
		}
	}

	/**
	 * Extract URLs from the classpath for creating an isolated class loader. Needed
	 * for Java 9+ where the system class loader is not a URLClassLoader.
	 */
	private java.net.URL[] getClasspathURLs() throws Exception {
		final String classpath = System.getProperty("java.class.path");
		final String[] entries = classpath.split(File.pathSeparator);
		final java.net.URL[] urls = new java.net.URL[entries.length];
		for (int i = 0; i < entries.length; i++) {
			urls[i] = new File(entries[i]).toURI().toURL();
		}
		return urls;
	}

	/**
	 * Runs TLC in an isolated class loader with a custom fingerprint and workers
	 * setting.
	 */
	private TLCResult runTLCInIsolation(String workingDir, String metaDir, String specFile, int fingerprint,
			String workers, String[] extraArgs, String... traceArgs) throws Exception {

		// Get the current class loader
		ClassLoader currentLoader = getClass().getClassLoader();

		// Extract URLs for the isolated class loader
		java.net.URL[] urls;
		if (currentLoader instanceof URLClassLoader) {
			// If we have a URLClassLoader, use its URLs
			urls = ((URLClassLoader) currentLoader).getURLs();
		} else {
			// Java 9+: Extract URLs from classpath
			urls = getClasspathURLs();
		}

		// Create an isolated class loader using the same approach as
		// IsolatedTestCaseRunner
		DumpLoadIsolatedClassLoader isolatedLoader = new DumpLoadIsolatedClassLoader(urls, currentLoader.getParent());

		try {
			// Set working directory in the isolated class loader
			Class<?> toolIOClass = isolatedLoader.loadClass("util.ToolIO");
			Method setUserDir = toolIOClass.getMethod("setUserDir", String.class);
			setUserDir.invoke(null, workingDir);

			// Create and set up the recorder in the isolated class loader
			Class<?> recorderClass = isolatedLoader.loadClass("tlc2.TestMPRecorder");
			Object recorderInstance = recorderClass.getDeclaredConstructor().newInstance();

			// Set the recorder via MP.setRecorder
			Class<?> mpClass = isolatedLoader.loadClass("tlc2.output.MP");
			Class<?> recorderInterface = isolatedLoader.loadClass("tlc2.output.IMessagePrinterRecorder");

			Method setRecorder = mpClass.getMethod("setRecorder", recorderInterface);
			setRecorder.invoke(null, recorderInstance);

			// Load TLC class in the isolated loader
			Class<?> tlcClass = isolatedLoader.loadClass("tlc2.TLC");

			// Create TLC instance
			Object tlcInstance = tlcClass.getDeclaredConstructor().newInstance();

			// Prepare arguments
			String[] args = buildArgs(metaDir, specFile, fingerprint, workers, extraArgs, traceArgs);

			// Call handleParameters(String[] args)
			Method handleParameters = tlcClass.getMethod("handleParameters", String[].class);
			handleParameters.invoke(tlcInstance, (Object) args);

			// Call process()
			Method process = tlcClass.getMethod("process");
			Object result = process.invoke(tlcInstance);
			int exitCode = (Integer) result;

			// Extract data from the recorder
			return new TLCResult(exitCode, recorderInstance, recorderClass);

		} finally {
			// Unregister all TLC MBeans to avoid conflicts in subsequent runs
			unregisterTLCMBeans();

			// Clean up class loader
			isolatedLoader.close();
		}
	}

	private void testDumpLoadTrace(String spec, String format, int expectedExitStatus, int expectedDumpStates,
			int expectedLoadStates) throws Exception {
		testDumpLoadTrace(spec, "", format, expectedExitStatus, expectedDumpStates, expectedLoadStates);
	}

	private void testDumpLoadTrace(String spec, String format, int expectedExitStatus, int expectedDumpStates,
			int expectedLoadStates, String dumpWorkers, String loadWorkers) throws Exception {
		testDumpLoadTrace(spec, "", format, expectedExitStatus, expectedDumpStates, expectedLoadStates, dumpWorkers,
				loadWorkers);
	}

	private void testDumpLoadTrace(String spec, String path, String format, int expectedExitStatus,
			int expectedDumpStates, int expectedLoadStates) throws Exception {
		testDumpLoadTrace(spec, path, new String[0], format, expectedExitStatus, expectedDumpStates,
				expectedLoadStates);
	}

	private void testDumpLoadTrace(String spec, String path, String format, int expectedExitStatus,
			int expectedDumpStates, int expectedLoadStates, String dumpWorkers, String loadWorkers) throws Exception {
		testDumpLoadTrace(spec, path, new String[0], format, expectedExitStatus, expectedDumpStates, expectedLoadStates,
				dumpWorkers, loadWorkers);
	}

	private void testDumpLoadTrace(final String spec, final String path, final String[] extraArgs, final String format,
			final int expectedExitStatus, final int expectedDumpStates, final int expectedLoadStates) throws Exception {
		testDumpLoadTrace(spec, path, extraArgs, format, expectedExitStatus, expectedDumpStates, expectedLoadStates,
				"1", "1");
	}

	private void testDumpLoadTrace(final String spec, final String path, final String[] extraArgs, final String format,
			final int expectedExitStatus, final int expectedDumpStates, final int expectedLoadStates,
			final String dumpWorkers, final String loadWorkers) throws Exception {
		// Setup temporary directories in target/ to avoid polluting the source tree
		final File targetDir = new File(BASE_DIR, "target");
		targetDir.mkdirs();
		tempDir = new File(targetDir, "dump-load-test-" + System.currentTimeMillis());
		tempDir.mkdirs();

		final File metaDump = new File(tempDir, "meta_dump");
		final File metaLoad = new File(tempDir, "meta_load");
		final File traceFile = new File(tempDir, spec + "." + format);

		metaDump.mkdirs();
		metaLoad.mkdirs();

		// Working directory for TLC (where it looks for imported modules)
		final String workingDir = BASE_PATH + (path.isEmpty() ? "" : path + File.separator);

		// Phase 1: Run TLC with -dumpTrace using isolated class loader
		final TLCResult dumpResult = runTLCInIsolation(workingDir, metaDump.getAbsolutePath(), spec + ".tla", 4,
				dumpWorkers, extraArgs, "-dumpTrace", format, traceFile.getAbsolutePath());

		assertTrue("Trace file should exist after dump phase", traceFile.exists());
		assertTrue("Trace file should not be empty", traceFile.length() > 0);
		assertTrue("Dump phase should have recorded TLC_FINISHED", dumpResult.recordedEC(EC.TLC_FINISHED));

		// Phase 2: Run TLC with -loadTrace using a different isolated class loader
		final TLCResult loadResult = runTLCInIsolation(workingDir, metaLoad.getAbsolutePath(), spec + ".tla", 4,
				loadWorkers, extraArgs, "-loadTrace", format, traceFile.getAbsolutePath());

		assertTrue("Load phase should have recorded TLC_FINISHED", loadResult.recordedEC(EC.TLC_FINISHED));

		// Assertions
		final int actualDumpStatus = EC.ExitStatus.errorConstantToExitStatus(dumpResult.exitCode);
		final int actualLoadStatus = EC.ExitStatus.errorConstantToExitStatus(loadResult.exitCode);

		assertEquals("Dump phase should produce expected exit status", expectedExitStatus, actualDumpStatus);
		assertEquals("Load phase should reproduce the same exit status", actualDumpStatus, actualLoadStatus);

		// Verify both runs found the same type of violation
		if (expectedExitStatus == EC.ExitStatus.VIOLATION_SAFETY) {
			assertEquals("Both runs should record same safety violation",
					dumpResult.recordedEC(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR),
					loadResult.recordedEC(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR));
		} else if (expectedExitStatus == EC.ExitStatus.VIOLATION_LIVENESS) {
			assertEquals("Both runs should record same liveness violation",
					dumpResult.recordedEC(EC.TLC_TEMPORAL_PROPERTY_VIOLATED),
					loadResult.recordedEC(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		}

		// Assert that both runs produced the expected error trace
		assertTrue("Dump phase should have recorded error trace", dumpResult.recordedEC(EC.TLC_STATE_PRINT2));
		assertTrue("Load phase should have recorded error trace", loadResult.recordedEC(EC.TLC_STATE_PRINT2));

		// Get the error traces from both runs
		final List<Object> dumpTrace = dumpResult.getRecords(EC.TLC_STATE_PRINT2);
		final List<Object> loadTrace = loadResult.getRecords(EC.TLC_STATE_PRINT2);

		// When dump and load use different worker counts, the load trace (single
		// worker)
		// may be a shorter counterexample (prefix) than the dump trace (multi-worker),
		// since multi-worker runs don't guarantee finding the shortest counterexample
		if (!dumpWorkers.equals(loadWorkers)) {
			assertTraceIsPrefix(dumpTrace, loadTrace);
		} else {
			// Same worker configuration should produce identical traces
			assertEquals("Both traces should have the same length", dumpTrace.size(), loadTrace.size());
			assertTracesEqual(dumpTrace, loadTrace);
		}

		// Verify the correct number of states were generated
		assertTrue("Dump phase should have recorded statistics", dumpResult.recordedEC(EC.TLC_STATS));
		assertTrue("Load phase should have recorded statistics", loadResult.recordedEC(EC.TLC_STATS));

		// Get stats: [states generated, distinct states, states left on queue]
		final String[] dumpStats = dumpResult.getStatsAsStrings();
		final String[] loadStats = loadResult.getStatsAsStrings();

		final int dumpStatesGenerated = Integer.parseInt(dumpStats[0]);
		final int loadStatesGenerated = Integer.parseInt(loadStats[0]);

		// Verify expected state counts (skip if negative values provided, e.g., for
		// auto-worker dump phase which is non-deterministic)
		if (expectedDumpStates >= 0) {
			assertEquals(String.format("Dump phase should generate expected states (spec: %s)", spec),
					expectedDumpStates, dumpStatesGenerated);
		}
		if (expectedLoadStates >= 0) {
			// When workers differ (e.g., dump with auto, load with 1), we check that the
			// load phase generates at least the expected minimum states. We cannot assume
			// the load phase will find the shortest counterexample, because if the dump
			// phase (with multiple workers) didn't find the shortest counterexample, then
			// the load phase is constrained by the dumped trace and cannot magically find a
			// shorter one. The dump phase provides an upper bound for what the load phase
			// can explore.
			if (!dumpWorkers.equals(loadWorkers)) {
				assertTrue(String.format(
						"Load phase should generate at least expected states (spec: %s, expected: %d, actual: %d)",
						spec, expectedLoadStates, loadStatesGenerated), loadStatesGenerated >= expectedLoadStates);
			} else {
				assertEquals(String.format("Load phase should generate expected states (spec: %s)", spec),
						expectedLoadStates, loadStatesGenerated);
			}
		}

		// The load phase should generate fewer or equal states than the dump phase
		// because it only follows the loaded trace (acting as a constraint). The dumped
		// trace provides an upper bound for the load phase's state space exploration.
		// Skip this check when expected counts are negative (auto-worker tests) or when
		// workers differ (since auto workers make dump phase non-deterministic).
		if (expectedDumpStates >= 0 && expectedLoadStates >= 0 && dumpWorkers.equals(loadWorkers)) {
			assertTrue(String.format("Load phase should not generate more states than dump phase (dump: %d, load: %d)",
					dumpStatesGenerated, loadStatesGenerated), loadStatesGenerated <= dumpStatesGenerated);
		}
	}

	@Test
	public void testLivenessMCDumpLoadTraceJSON() throws Exception {
		testDumpLoadTrace("MC", "CodePlexBug08", new String[] { "-deadlock" }, "json", EC.ExitStatus.VIOLATION_LIVENESS,
				18, 13);
	}

	@Test
	public void testLivenessMCDumpLoadTraceTLC() throws Exception {
		testDumpLoadTrace("MC", "CodePlexBug08", new String[] { "-deadlock" }, "tlc", EC.ExitStatus.VIOLATION_LIVENESS,
				18, 13);
	}

	@Test
	public void testLivenessMCDumpLoadTraceJSONAutoWorkers() throws Exception {
		testDumpLoadTrace("MC", "CodePlexBug08", new String[] { "-deadlock" }, "json", EC.ExitStatus.VIOLATION_LIVENESS,
				-1, 13, "auto", "1");
	}

	@Test
	public void testLivenessMCDumpLoadTraceTLCAutoWorkers() throws Exception {
		testDumpLoadTrace("MC", "CodePlexBug08", new String[] { "-deadlock" }, "tlc", EC.ExitStatus.VIOLATION_LIVENESS,
				-1, 13, "auto", "1");
	}

	@Test
	@Ignore("Disabled because JSON trace serialization is garbled because of limited types.")
	public void testLivenessEWD840MC3DumpLoadTraceJSON() throws Exception {
		testDumpLoadTrace("EWD840MC3", "CodePlexBug08", new String[] { "-deadlock" }, "json",
				EC.ExitStatus.VIOLATION_LIVENESS, 15986, 7154);
	}

	@Test
	public void testLivenessEWD840MC3DumpLoadTraceTLC() throws Exception {
		testDumpLoadTrace("EWD840MC3", "CodePlexBug08", new String[] { "-deadlock" }, "tlc",
				EC.ExitStatus.VIOLATION_LIVENESS, 15986, 7154);
	}

	@Test
	public void testLivenessEWD840MC3DumpLoadTraceTLCAutoWorkers() throws Exception {
		testDumpLoadTrace("EWD840MC3", "CodePlexBug08", new String[] { "-deadlock" }, "tlc",
				EC.ExitStatus.VIOLATION_LIVENESS, -1, 7154, "auto", "1");
	}

	@Test
	public void testSafetyDumpLoadTraceJSON() throws Exception {
		testDumpLoadTrace("DieHard", "json", EC.ExitStatus.VIOLATION_SAFETY, 252, 36);
	}

	@Test
	public void testSafetyDumpLoadTraceTLC() throws Exception {
		testDumpLoadTrace("DieHard", "tlc", EC.ExitStatus.VIOLATION_SAFETY, 252, 36);
	}

	@Test
	public void testSafetyDumpLoadTraceJSONAutoWorkers() throws Exception {
		testDumpLoadTrace("DieHard", "json", EC.ExitStatus.VIOLATION_SAFETY, -1, 36, "auto", "1");
	}

	@Test
	public void testSafetyDumpLoadTraceTLCAutoWorkers() throws Exception {
		testDumpLoadTrace("DieHard", "tlc", EC.ExitStatus.VIOLATION_SAFETY, -1, 36, "auto", "1");
	}

	@Test
	public void testLivenessBidirectionalDumpLoadTraceJSON() throws Exception {
		testDumpLoadTrace("BidirectionalTransitions", "", new String[] { "-config", "BidirectionalTransitions1Bx.cfg" },
				"json", EC.ExitStatus.VIOLATION_LIVENESS, 13, 13);
	}

	@Test
	public void testLivenessBidirectionalDumpLoadTraceTLC() throws Exception {
		testDumpLoadTrace("BidirectionalTransitions", "", new String[] { "-config", "BidirectionalTransitions1Bx.cfg" },
				"tlc", EC.ExitStatus.VIOLATION_LIVENESS, 13, 13);
	}

	@Test
	public void testLivenessBidirectionalDumpLoadTraceJSONAutoWorkers() throws Exception {
		testDumpLoadTrace("BidirectionalTransitions", "", new String[] { "-config", "BidirectionalTransitions1Bx.cfg" },
				"json", EC.ExitStatus.VIOLATION_LIVENESS, -1, 13, "auto", "1");
	}

	@Test
	public void testLivenessBidirectionalDumpLoadTraceTLCAutoWorkers() throws Exception {
		testDumpLoadTrace("BidirectionalTransitions", "", new String[] { "-config", "BidirectionalTransitions1Bx.cfg" },
				"tlc", EC.ExitStatus.VIOLATION_LIVENESS, -1, 13, "auto", "1");
	}

	@Test
	public void testSafetyTESpecEqAliasDumpLoadTraceJSON() throws Exception {
		testDumpLoadTrace("TESpecTest", "TESpecTest", new String[] { "-config", "TESpecEqAliasSafetyTest.cfg" },
				"json", EC.ExitStatus.VIOLATION_SAFETY, 5, 5);
	}

	@Test
	public void testSafetyTESpecEqAliasDumpLoadTraceTLC() throws Exception {
		testDumpLoadTrace("TESpecTest", "TESpecTest", new String[] { "-config", "TESpecEqAliasSafetyTest.cfg" },
				"tlc", EC.ExitStatus.VIOLATION_SAFETY, 5, 5);
	}

	@Test
	public void testSafetyTESpecEqAliasDumpLoadTraceJSONAutoWorkers() throws Exception {
		testDumpLoadTrace("TESpecTest", "TESpecTest", new String[] { "-config", "TESpecEqAliasSafetyTest.cfg" },
				"json", EC.ExitStatus.VIOLATION_SAFETY, -1, 5, "auto", "1");
	}

	@Test
	public void testSafetyTESpecEqAliasDumpLoadTraceTLCAutoWorkers() throws Exception {
		testDumpLoadTrace("TESpecTest", "TESpecTest", new String[] { "-config", "TESpecEqAliasSafetyTest.cfg" },
				"tlc", EC.ExitStatus.VIOLATION_SAFETY, -1, 5, "auto", "1");
	}

	@Test
	public void testLivenessExample1DumpLoadTraceJSON() throws Exception {
		testDumpLoadTrace("Example1", "simulation", new String[] { "-config", "Example1.cfg" },
				"json", EC.ExitStatus.VIOLATION_LIVENESS, 11, 11);
	}

	@Test
	public void testLivenessExample1DumpLoadTraceTLC() throws Exception {
		testDumpLoadTrace("Example1", "simulation", new String[] { "-config", "Example1.cfg" },
				"tlc", EC.ExitStatus.VIOLATION_LIVENESS, 11, 11);
	}

	@Test
	public void testLivenessExample1DumpLoadTraceJSONAutoWorkers() throws Exception {
		testDumpLoadTrace("Example1", "simulation", new String[] { "-config", "Example1.cfg" },
				"json", EC.ExitStatus.VIOLATION_LIVENESS, -1, 11, "auto", "1");
	}

	@Test
	public void testLivenessExample1DumpLoadTraceTLCAutoWorkers() throws Exception {
		testDumpLoadTrace("Example1", "simulation", new String[] { "-config", "Example1.cfg" },
				"tlc", EC.ExitStatus.VIOLATION_LIVENESS, -1, 11, "auto", "1");
	}

	/**
	 * Unregister all TLC-related MBeans from the platform MBeanServer.
	 * 
	 * <p>
	 * <b>Why this is necessary:</b>
	 * </p>
	 * 
	 * <p>
	 * This test runs TLC twice in succession (dump phase, then load phase) using
	 * isolated class loaders to ensure complete static state isolation. However,
	 * JMX MBeans are registered in the <b>JVM-global platform MBeanServer</b>,
	 * which is a singleton shared across all class loaders.
	 * </p>
	 * 
	 * <p>
	 * When the dump phase runs, TLC registers MBeans like:
	 * <ul>
	 * <li>{@code tlc2.tool.liveness:type=StronglyConnectedComponent sizes}</li>
	 * <li>{@code tlc2.tool:type=ModelChecker}</li>
	 * <li>etc.</li>
	 * </ul>
	 * </p>
	 * 
	 * <p>
	 * These MBeans persist even after the isolated class loader is closed. When the
	 * load phase tries to register MBeans with the same names, it fails with:
	 * {@code javax.management.InstanceAlreadyExistsException}
	 * </p>
	 * 
	 * <p>
	 * This method cleans up all TLC MBeans between test phases to prevent
	 * registration conflicts. Without this cleanup, liveness tests fail because
	 * they trigger MBean registration in {@code LiveWorker.<clinit>}.
	 * </p>
	 */
	private void unregisterTLCMBeans() {
		try {
			MBeanServer mbs = java.lang.management.ManagementFactory.getPlatformMBeanServer();

			// Find all TLC-related MBeans (they start with "tlc2.")
			Set<ObjectName> mbeans = mbs.queryNames(new ObjectName("tlc2.*:*"), null);

			for (ObjectName name : mbeans) {
				try {
					mbs.unregisterMBean(name);
				} catch (Exception e) {
					// Ignore errors during cleanup
					System.err.println("Warning: Could not unregister MBean: " + name + " - " + e.getMessage());
				}
			}
		} catch (Exception e) {
			// Ignore errors during cleanup
			System.err.println("Warning: Error during MBean cleanup: " + e.getMessage());
		}
	}
}
