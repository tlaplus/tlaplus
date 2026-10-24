package tlc2.tool.simulation;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.InputStream;
import java.util.Arrays;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.Before;
import org.junit.Test;

import tlc2.tool.CommonTestCase;
import util.ToolIO;

/**
 * End-to-end regression test for https://github.com/tlaplus/tlaplus/issues/1485
 * that runs TLC's -generate mode in a separate JVM, with the probabilistic
 * system property actually set.
 *
 * Github1485Test checks the successor state distribution of the very same
 * specs in-process, but it cannot flip the
 * tlc2.tool.impl.Tool.probabilistic system property for an already loaded
 * Tool class. This test instead observes how many successor states TLC
 * generates per step of a behavior: uniform successor selection evaluates the
 * complete next-state relation, i.e. Github1485Disj reports five generated
 * states per step (plus one initial state), whereas a "first found" selection
 * that stops at the first successor generates close to one state per step.
 */
public class Github1485GenerateTest extends CommonTestCase {

	private static final Pattern STATES_GENERATED = Pattern
			.compile("The number of states generated: (\\d+)");

	public Github1485GenerateTest() {
		// No recorder because the subprocess output is captured below.
		super(null);
	}

	@Before
	public void setUp() {
		ToolIO.setUserDir(BASE_PATH + File.separator + "simulation" + File.separator + "Github1485");
	}

	/**
	 * Runs TLC -generate on the given spec in a fresh JVM (the probabilistic
	 * system property is static final in Tool and can only be set before the
	 * class gets loaded) and returns its combined stdout/stderr.
	 */
	private String runTLCGenerate(final String spec, final String generateOptions, final String... jvmOptions)
			throws Exception {
		// The classpath of this JVM's entries is relative to its working
		// directory, but the subprocess runs in the spec's directory.
		final String userDir = System.getProperty("user.dir");
		final StringBuilder cp = new StringBuilder();
		for (final String entry : System.getProperty("java.class.path").split(File.pathSeparator)) {
			if (cp.length() > 0) {
				cp.append(File.pathSeparator);
			}
			cp.append(new File(entry).isAbsolute() ? entry : userDir + File.separator + entry);
		}

		final ProcessBuilder pb = new ProcessBuilder(javaExecutable(), "-Xmx64m",
				"-Dtlc2.tool.impl.Tool.probabilistic=true",
				"-cp", cp.toString(), "tlc2.TLC",
				"-generate", generateOptions, "-depth", "1", "-seed", "7",
				"-workers", "1", "-noGenerateSpecTE", spec);
		pb.command().addAll(1, Arrays.asList(jvmOptions));
		pb.directory(new File(ToolIO.getUserDir()));
		return runProcess(pb.redirectErrorStream(true).start(), 120);
	}

	private static String javaExecutable() {
		final boolean windows = System.getProperty("os.name").toLowerCase().contains("win");
		return System.getProperty("java.home") + File.separator + "bin" + File.separator + "java"
				+ (windows ? ".exe" : "");
	}

	private String runProcess(final Process process, final long timeoutSeconds) throws Exception {
		final ExecutorService reader = Executors.newSingleThreadExecutor();
		try {
			// Drain output concurrently so neither a full pipe nor an EOF read defeats the timeout.
			final Future<byte[]> captured = reader.submit(() -> {
				try (InputStream output = process.getInputStream()) {
					return output.readAllBytes();
				}
			});
			final boolean finished;
			try {
				finished = process.waitFor(timeoutSeconds, TimeUnit.SECONDS);
			} finally {
				if (process.isAlive()) {
					process.destroyForcibly();
					assertTrue("TLC process could not be terminated", process.waitFor(10, TimeUnit.SECONDS));
				}
			}
			final String output = new String(captured.get(10, TimeUnit.SECONDS));
			assertTrue("TLC did not terminate in time:\n" + output, finished);
			assertEquals("TLC exited with an error:\n" + output, 0, process.exitValue());
			return output;
		} finally {
			reader.shutdownNow();
		}
	}

	private static long statesGenerated(final String output) {
		final Matcher matcher = STATES_GENERATED.matcher(output);
		assertTrue("No state count reported:\n" + output, matcher.find());
		return Long.parseLong(matcher.group(1));
	}

	@Test
	public void testGeneratesAllSuccessorStates() throws Exception {
		final String output = runTLCGenerate("Github1485Disj", "num=200");
		assertTrue("No progress reported for Github1485Disj:\n" + output,
				output.contains("200 traces generated"));

		// With the complete next-state relation evaluated, every one of the
		// 200 steps generates five successor states, plus one initial state:
		// 1001. If a "first found" selection --the bug reported in issue
		// 1485-- gets reintroduced, only about one successor state per step
		// gets generated, i.e. roughly 201.
		final long statesGenerated = statesGenerated(output);
		assertTrue("Expected at least 1000 generated states (full enumeration) but was " + statesGenerated,
				statesGenerated >= 1000);
	}

	@Test
	public void testCaseNextStateRelation() throws Exception {
		// -generate used to reject a next-state relation whose top-level
		// operator is CASE ("Probabilistic evaluation of next-state relation
		// not implemented for CASE yet.").
		final String output = runTLCGenerate("Github1485Case", "num=200");
		assertTrue("CASE next-state relation rejected again:\n" + output,
				!output.contains("not implemented for CASE"));
		assertTrue("No progress reported for Github1485Case:\n" + output,
				output.contains("200 traces generated"));
	}

	@Test
	public void testRLSchedulersUseBoundedSuccessorMemory() throws Exception {
		for (final String scheduler : new String[] { "rl", "rlaction" }) {
			for (final boolean enabledOnly : new boolean[] { false, true }) {
				final String output = runTLCGenerate("Github1485HighFanout", "num=1,sched=" + scheduler,
						"-Dtlc2.tool.Simulator.rl.enabledOnly=" + enabledOnly);
				assertEquals("All successors must be enumerated with scheduler " + scheduler,
						1000001L, statesGenerated(output));
			}
		}
	}

	@Test
	public void testRLSchedulersOnlyEvaluateChosenAction() throws Exception {
		for (final String scheduler : new String[] { "rl", "rlaction" }) {
			final String output = runTLCGenerate("Github1485Disj", "num=200,sched=" + scheduler);
			final long states = statesGenerated(output);
			// The chosen action has one or four successors; evaluating both would yield 1001.
			assertTrue("Unexpected state count for scheduler " + scheduler + ": " + states,
					states >= 201 && states <= 801);
		}
	}

	@Test
	public void testProcessTimeout() throws Exception {
		final ProcessBuilder pb = new ProcessBuilder(javaExecutable(), "-cp",
				System.getProperty("java.class.path"), SleepingProcess.class.getName());
		final Process unrelated = pb.start();
		try {
			final Process process = pb.redirectErrorStream(true).start();
			try {
				runProcess(process, 1);
				fail("Expected the child process to time out");
			} catch (final AssertionError e) {
				assertTrue(e.getMessage(), e.getMessage().startsWith("TLC did not terminate in time:\n"));
			}
			assertFalse("Timed out child process was not reaped", process.isAlive());
			assertTrue("Unrelated child process was terminated", unrelated.isAlive());
		} finally {
			unrelated.destroyForcibly();
			assertTrue("Unrelated child process could not be terminated", unrelated.waitFor(10, TimeUnit.SECONDS));
		}
	}

	public static final class SleepingProcess {
		public static void main(final String[] args) throws Exception {
			Thread.sleep(TimeUnit.SECONDS.toMillis(30));
		}
	}
}
