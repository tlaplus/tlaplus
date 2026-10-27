/*******************************************************************************
 * Copyright (c) 2026 Matt Van Horn.
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
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 ******************************************************************************/
package tlc2.tool.checkpoint;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.lang.reflect.Field;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;

import org.junit.After;
import org.junit.Test;

import tlc2.TLC;
import tlc2.TLCGlobals;
import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.AbstractChecker;
import tlc2.tool.CommonTestCase;
import tlc2.tool.ModelChecker;
import tlc2.tool.TLCStateInfo;
import tlc2.util.FP64;
import tlc2.value.RandomEnumerableValues;
import util.FileUtil;
import util.InternTable;
import util.ToolIO;
import util.UniqueString;

/**
 * Recovery must keep working when fingerprint, seed, and worker settings match
 * the checkpoint, and must warn — without changing the requested settings —
 * when they do not or when the sidecar cannot be checked.
 */
public class CheckpointRecoverySettingsTest extends CommonTestCase {

	static {
		// Read by ModelChecker when that class is initialized. Set it before any
		// active use so successful runs keep the checkpoint directory.
		System.setProperty("tlc2.tool.ModelChecker.vetoCleanup", "true");
	}

	private static final long SEED = 42L;
	private static final int FP = 2;
	private static final int WORKERS = 1;
	/** A checkpoint interval long enough that only explicit cleanup checkpoints fire. */
	private static final int CHECKPOINT_MINUTES = Integer.MAX_VALUE / 60000;

	private final long savedSeed = RandomEnumerableValues.getSeed();
	private final long savedPoly = FP64.getIrredPoly();
	private final int savedWorkers = TLCGlobals.getNumWorkers();
	private final long savedChkpt = TLCGlobals.chkptDuration;
	private final String savedMetaDir = TLCGlobals.metaDir;
	private final String savedLnCheck = TLCGlobals.lnCheck;
	private final String savedUserDir = ToolIO.getUserDir();
	private final List<File> scratch = new ArrayList<File>();
	private int copySeq;

	@After
	public void restoreGlobals() {
		RandomEnumerableValues.setSeed(savedSeed);
		FP64.Init(savedPoly);
		TLCGlobals.setNumWorkers(savedWorkers);
		TLCGlobals.chkptDuration = savedChkpt;
		TLCGlobals.metaDir = savedMetaDir;
		TLCGlobals.lnCheck = savedLnCheck;
		ToolIO.setUserDir(savedUserDir);
		System.clearProperty(TLC.class.getName() + ".stopAfter");
		resetDefinitionLocs();
		for (File dir : scratch) {
			FileUtil.deleteDir(dir, true);
		}
	}

	@Test
	public void testRecoverySettings() throws Exception {
		final File root = scratchDir("diehard");
		final Run created = run("DieHard", BASE_PATH, new File(root, "create"), null, SEED, FP, WORKERS);
		assertEquals(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, created.errorCode);
		assertTrue(created.recorder.recorded(EC.TLC_CHECKPOINT_END));
		assertTrue(created.recorder.recorded(EC.TLC_STATE_PRINT2));
		assertFalse(created.recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_REVISION_MISMATCH));
		assertCommittedSettings(created.checkpoint, SEED, FP, WORKERS);
		assertFalse(settingsFile(created.checkpoint, "tmp").exists());
		final String[] stats = stats(created);

		final Run matching = recover(created.checkpoint, "matching", SEED, FP, WORKERS);
		assertNoSettingsWarning(matching);
		assertEquals(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, matching.errorCode);
		assertTrue(matching.recorder.recordedWithStringValues(EC.TLC_CHECKPOINT_RECOVER_END, stats[1], stats[2]));
		// The checkpoint is taken after the first counterexample, so recovery
		// continues and reports the next violation rather than that same trace.
		assertFalse(trace(matching).isEmpty());

		assertMismatch(recover(created.checkpoint, "seed", 99L, FP, WORKERS),
				SEED, FP, WORKERS, 99L, FP, WORKERS, "seed");
		assertMismatch(recover(created.checkpoint, "fp", SEED, FP + 1, WORKERS),
				SEED, FP, WORKERS, SEED, FP + 1, WORKERS, "fingerprint");
		assertMismatch(recover(created.checkpoint, "workers", SEED, FP, WORKERS + 1),
				SEED, FP, WORKERS, SEED, FP, WORKERS + 1, "workers");
		final Run all = recover(created.checkpoint, "all", 7L, FP + 1, WORKERS + 2);
		assertMismatch(all, SEED, FP, WORKERS, 7L, FP + 1, WORKERS + 2, "seed, fingerprint, workers");
		assertEquals(1, all.recorder.getRecords(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_MISMATCH).size());
		final String diagnostic = MP.getMessage(MP.WARNING, EC.TLC_CHECKPOINT_RECOVER_SETTINGS_MISMATCH,
				(String[]) all.recorder.getRecords(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_MISMATCH).get(0));
		assertTrue(diagnostic.contains("Results may be unreliable."));
		assertTrue(diagnostic.contains("-seed " + SEED + " -fp " + FP + " -workers " + WORKERS));
		assertTrue(diagnostic.contains("-seed 7 -fp " + (FP + 1) + " -workers " + (WORKERS + 2)));

		final Run legacy = recoverCopy(created.checkpoint, "legacy", SEED, FP, WORKERS, new CopyEditor() {
			public void edit(File dir) throws IOException {
				assertTrue(settingsFile(dir, "chkpt").delete());
				// A temporary settings file must not be treated as committed metadata.
				write(settingsFile(dir, "tmp"), settings(1, 777L, 0, FP64.Polys[0], 9));
			}
		});
		assertNoSettingsWarning(legacy);
		assertTrue(legacy.recorder.recordedWithStringValues(EC.TLC_CHECKPOINT_RECOVER_END, stats[1], stats[2]));
		assertEquals(trace(matching), trace(legacy));
		assertEquals(matching.errorCode, legacy.errorCode);

		assertUnverifiable(created.checkpoint, "truncated", "version=1\nseed=" + SEED + "\n", SEED, FP, WORKERS);
		assertUnverifiable(created.checkpoint, "malformed",
				"version=1\nseed=nope\nfpIndex=" + FP + "\nfp=" + FP64.Polys[FP] + "\nworkers=" + WORKERS + "\n",
				SEED, FP, WORKERS);
		assertUnverifiable(created.checkpoint, "unsupported version",
				settings(99, SEED, FP, FP64.Polys[FP], WORKERS), SEED, FP, WORKERS);
		assertUnverifiable(created.checkpoint, "invalid fingerprint",
				settings(1, SEED, FP, FP64.Polys[FP + 1], WORKERS), SEED, FP, WORKERS);
		assertUnverifiable(created.checkpoint, "invalid fingerprint",
				settings(1, SEED, 100000, FP64.Polys[FP], WORKERS), SEED, FP, WORKERS);
		assertUnverifiable(created.checkpoint, "invalid workers",
				settings(1, SEED, FP, FP64.Polys[FP], 0), SEED, FP, WORKERS);
		assertUnverifiable(created.checkpoint, "invalid workers",
				settings(1, SEED, FP, FP64.Polys[FP], -1), SEED, FP, WORKERS);
	}

	@Test
	public void testPeriodicAndCleanupCheckpoints() throws Exception {
		final File root = scratchDir("periodic");
		final File meta = new File(root, "meta");
		assertTrue(meta.mkdirs());
		System.setProperty(TLC.class.getName() + ".stopAfter", "20");
		resetDefinitionLocs();
		TLCGlobals.metaDir = null;
		final TestMPRecorder rec = new TestMPRecorder();
		MP.setRecorder(rec);
		ToolIO.setUserDir(BASE_PATH + "checkpoint");
		final TLC tlc = new TLC();
		final List<String> args = baseArgs(SEED, FP, WORKERS);
		args.add("-metadir");
		args.add(meta.getAbsolutePath());
		args.add("InfiniteStateSpace");
		try {
			assertTrue(tlc.handleParameters(args.toArray(new String[args.size()])));
			TLCGlobals.chkptDuration = 1L;
			final int[] code = new int[] { -1 };
			final Thread runner = new Thread(new Runnable() {
				public void run() {
					code[0] = tlc.process();
				}
			}, "periodic-checkpoint");
			runner.start();
			final File checkpoint = waitForChildDir(meta);
			waitUntilExploring();
			assertEquals(EC.NO_ERROR, ((ModelChecker) TLCGlobals.mainChecker).doPeriodicWork());
			assertCommittedSettings(checkpoint, SEED, FP, WORKERS);
			// An in-progress settings file must not become the committed sidecar.
			write(settingsFile(checkpoint, "tmp"), settings(1, 777L, 0, FP64.Polys[0], 9));
			((ModelChecker) TLCGlobals.mainChecker).stop();
			runner.join(20000);
			assertFalse(runner.isAlive());
			assertEquals(EC.NO_ERROR, code[0]);
			assertTrue(rec.recorded(EC.TLC_CHECKPOINT_END));
			assertTrue(rec.getRecords(EC.TLC_CHECKPOINT_END).size() >= 2);
			assertCommittedSettings(checkpoint, SEED, FP, WORKERS);
			assertFalse(settingsFile(checkpoint, "tmp").isFile());
			assertNoSettingsWarning(rec);
		} finally {
			MP.unsubscribeRecorder(rec);
			System.clearProperty(TLC.class.getName() + ".stopAfter");
		}
	}

	private interface CopyEditor {
		void edit(File dir) throws IOException;
	}

	private static final class Run {
		final TestMPRecorder recorder;
		final int errorCode;
		final File checkpoint;

		Run(TestMPRecorder recorder, int errorCode, File checkpoint) {
			this.recorder = recorder;
			this.errorCode = errorCode;
			this.checkpoint = checkpoint;
		}
	}

	private Run recover(File checkpoint, String name, long seed, int fp, int workers) throws Exception {
		return recoverCopy(checkpoint, name, seed, fp, workers, null);
	}

	private Run recoverCopy(File checkpoint, String name, long seed, int fp, int workers, CopyEditor editor)
			throws Exception {
		final File copy = new File(checkpoint.getParentFile().getParentFile(), name + "-" + (copySeq++));
		copyDir(checkpoint, copy);
		if (editor != null) {
			editor.edit(copy);
		}
		return run("DieHard", BASE_PATH, null, copy, seed, fp, workers);
	}

	private void assertUnverifiable(File checkpoint, final String reason, final String body, long seed, int fp,
			int workers) throws Exception {
		final Run run = recoverCopy(checkpoint, "bad-" + reason.replace(' ', '-'), seed, fp, workers, new CopyEditor() {
			public void edit(File dir) throws IOException {
				write(settingsFile(dir, "chkpt"), body);
			}
		});
		assertTrue(reason, run.recorder.recordedWithStringValue(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_UNVERIFIABLE, reason));
		assertEquals(reason, 1, run.recorder.getRecords(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_UNVERIFIABLE).size());
		assertFalse(run.recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_MISMATCH));
		assertTrue(run.recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_END));
		final String message = MP.getMessage(MP.WARNING, EC.TLC_CHECKPOINT_RECOVER_SETTINGS_UNVERIFIABLE,
				new String[] { reason });
		assertTrue(message.contains("could not be verified (" + reason + ")"));
		assertTrue(message.contains("Results may be unreliable."));
	}

	private void assertMismatch(Run run, long originalSeed, int originalFp, int originalWorkers, long currentSeed,
			int currentFp, int currentWorkers, String changed) {
		assertTrue(run.recorder.recordedWithStringValues(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_MISMATCH,
				Long.toString(originalSeed), Integer.toString(originalFp), Integer.toString(originalWorkers),
				Long.toString(FP64.Polys[originalFp]), Long.toString(currentSeed), Integer.toString(currentFp),
				Integer.toString(currentWorkers), Long.toString(FP64.Polys[currentFp]), changed));
		assertFalse(run.recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_UNVERIFIABLE));
		assertTrue(run.recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_START));
	}

	private static void assertNoSettingsWarning(Run run) {
		assertNoSettingsWarning(run.recorder);
	}

	private static void assertNoSettingsWarning(TestMPRecorder rec) {
		assertFalse(rec.recorded(EC.TLC_CHECKPOINT_RECOVER_REVISION_MISMATCH));
		assertFalse(rec.recorded(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_MISMATCH));
		assertFalse(rec.recorded(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_UNVERIFIABLE));
	}

	private static void assertCommittedSettings(File dir, long seed, int fp, int workers) throws IOException {
		final List<String> lines = Files.readAllLines(settingsFile(dir, "chkpt").toPath(), StandardCharsets.UTF_8);
		assertEquals((settings(1, seed, fp, FP64.Polys[fp], workers) + "revision=" + TLCGlobals.Version.revisionOrDev()).trim(), join(lines));
		assertEquals(Long.toString(RandomEnumerableValues.getSeed()), Long.toString(seed));
		assertEquals(FP64.Polys[fp], FP64.getIrredPoly());
		assertEquals(workers, TLCGlobals.getNumWorkers());
	}

	/**
	 * Operator and variable slots live on the interned name. A later spec must not
	 * reuse a slot assigned by an earlier one. The intern table itself stays, so
	 * the parser's operator table keeps its original keys.
	 */
	private static void resetDefinitionLocs() {
		try {
			UniqueString.setVariableCount(0);
			final Field table = InternTable.class.getDeclaredField("table");
			table.setAccessible(true);
			final UniqueString[] entries = (UniqueString[]) table.get(UniqueString.internTbl);
			final Field loc = UniqueString.class.getDeclaredField("loc");
			loc.setAccessible(true);
			if (entries == null) {
				return;
			}
			for (UniqueString entry : entries) {
				if (entry != null) {
					loc.setInt(entry, -1);
				}
			}
		} catch (ReflectiveOperationException e) {
			throw new IllegalStateException(e);
		}
	}

	private Run run(String spec, String specDir, File metaParent, File recoverFrom, long seed, int fp, int workers)
			throws Exception {
		resetDefinitionLocs();
		TLCGlobals.metaDir = null;
		final TestMPRecorder rec = new TestMPRecorder();
		MP.setRecorder(rec);
		ToolIO.setUserDir(specDir);
		final TLC tlc = new TLC();
		final List<String> args = baseArgs(seed, fp, workers);
		if (recoverFrom != null) {
			args.add("-recover");
			args.add(recoverFrom.getAbsolutePath());
		} else {
			args.add("-metadir");
			args.add(metaParent.getAbsolutePath());
		}
		args.add(spec);
		try {
			assertTrue(args.toString(), tlc.handleParameters(args.toArray(new String[args.size()])));
			final int code = tlc.process();
			final File checkpoint = recoverFrom != null ? recoverFrom : soleChild(metaParent);
			return new Run(rec, code, checkpoint);
		} finally {
			MP.unsubscribeRecorder(rec);
		}
	}

	private static List<String> baseArgs(long seed, int fp, int workers) {
		final List<String> args = new ArrayList<String>();
		args.add("-deadlock");
		args.add("-noGenerateSpecTE");
		args.add("-lncheck");
		args.add("off");
		args.add("-workers");
		args.add(Integer.toString(workers));
		args.add("-fp");
		args.add(Integer.toString(fp));
		args.add("-seed");
		args.add(Long.toString(seed));
		args.add("-checkpoint");
		args.add(Integer.toString(CHECKPOINT_MINUTES));
		return args;
	}

	private static String[] stats(Run run) {
		final Object record = run.recorder.getRecords(EC.TLC_STATS).get(0);
		return (String[]) record;
	}

	private static List<String> trace(Run run) {
		final List<String> states = new ArrayList<String>();
		final List<Object> records = run.recorder.getRecords(EC.TLC_STATE_PRINT2);
		if (records == null) {
			return states;
		}
		for (Object record : records) {
			final Object[] fields = (Object[]) record;
			states.add(((TLCStateInfo) fields[0]).toString().trim());
		}
		return states;
	}

	private File scratchDir(String name) throws IOException {
		final File dir = Files.createTempDirectory("tlc-checkpoint-settings-" + name).toFile();
		scratch.add(dir);
		return dir;
	}

	private static File soleChild(File parent) {
		final File[] children = parent.listFiles(File::isDirectory);
		assertNotNull(parent.getAbsolutePath(), children);
		assertEquals(parent.getAbsolutePath(), 1, children.length);
		return children[0];
	}

	private static File waitForChildDir(File parent) throws InterruptedException {
		final long deadline = System.currentTimeMillis() + 20000L;
		while (System.currentTimeMillis() < deadline) {
			final File[] children = parent.listFiles(File::isDirectory);
			if (children != null && children.length == 1) {
				return children[0];
			}
			Thread.sleep(20L);
		}
		fail("Checkpoint directory was not created under " + parent);
		return null;
	}

	private static void waitUntilExploring() throws InterruptedException {
		final long deadline = System.currentTimeMillis() + 20000L;
		while (System.currentTimeMillis() < deadline) {
			final AbstractChecker checker = TLCGlobals.mainChecker;
			if (checker instanceof ModelChecker
					&& checker.getStatesGenerated() > checker.getInitialStatesGenerated()) {
				return;
			}
			Thread.sleep(20L);
		}
		fail("Model checking did not start exploring successor states");
	}

	private static File settingsFile(File dir, String ext) {
		return new File(dir, "tmp".equals(ext) ? "settings.tmp.chkpt" : "settings.chkpt");
	}

	private static String settings(int version, long seed, int fpIndex, long fp, int workers) {
		return "version=" + version + "\n"
				+ "seed=" + seed + "\n"
				+ "fpIndex=" + fpIndex + "\n"
				+ "fp=" + fp + "\n"
				+ "workers=" + workers + "\n";
	}

	private static void write(File file, String body) throws IOException {
		Files.write(file.toPath(), body.getBytes(StandardCharsets.UTF_8));
	}

	private static String join(List<String> lines) {
		final StringBuilder text = new StringBuilder();
		for (int i = 0; i < lines.size(); i++) {
			if (i > 0) {
				text.append('\n');
			}
			text.append(lines.get(i));
		}
		return text.toString();
	}

	private static void copyDir(File src, File dest) throws IOException {
		if (src.isDirectory()) {
			if (!dest.exists() && !dest.mkdirs()) {
				throw new IOException("Cannot create " + dest);
			}
			final File[] children = src.listFiles();
			assertNotNull(children);
			for (File child : children) {
				copyDir(child, new File(dest, child.getName()));
			}
		} else {
			Files.copy(src.toPath(), dest.toPath());
		}
	}
}
