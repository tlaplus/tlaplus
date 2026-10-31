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
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;

import org.junit.After;
import org.junit.Test;

import tlc2.TestMPRecorder;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.CheckpointSettings;
import tlc2.tool.CheckpointSettings.Values;
import tlc2.util.FP64;
import tlc2.value.RandomEnumerableValues;
import util.FileUtil;

/**
 * Round-trip the checkpoint settings sidecar without running TLC.
 */
public class CheckpointSettingsTest {

	private static final long SEED = 42L;
	private static final int FP = 2;
	private static final int WORKERS = 3;

	private final long savedSeed = RandomEnumerableValues.getSeed();
	private final long savedPoly = FP64.getIrredPoly();
	private final List<File> scratch = new ArrayList<File>();
	private TestMPRecorder recorder;

	@After
	public void cleanup() {
		RandomEnumerableValues.setSeed(savedSeed);
		FP64.Init(savedPoly);
		if (recorder != null) {
			MP.unsubscribeRecorder(recorder);
			recorder = null;
		}
		for (File dir : scratch) {
			FileUtil.deleteDir(dir, true);
		}
	}

	@Test
	public void testRoundTrip() throws Exception {
		final File dir = scratchDir();
		install(SEED, FP);
		final CheckpointSettings settings = new CheckpointSettings(dir.getAbsolutePath(), WORKERS);

		settings.beginChkpt();
		assertTrue(file(dir, "tmp").isFile());
		assertFalse(file(dir, "chkpt").exists());
		// An uncommitted temporary sidecar is not recovered.
		assertNull(settings.recover());
		assertNoSettingsWarning();

		settings.commitChkpt();
		assertFalse(file(dir, "tmp").exists());
		assertEquals(text(SEED, FP, WORKERS), read(file(dir, "chkpt")));

		final Values recovered = settings.recover();
		assertValues(recovered, SEED, FP, WORKERS);
		assertEquals(SEED, RandomEnumerableValues.getSeed());
		assertEquals(FP64.Polys[FP], FP64.getIrredPoly());
		assertNoSettingsWarning();

		// commit replaces the previous sidecar.
		install(99L, FP + 1);
		settings.beginChkpt();
		settings.commitChkpt();
		assertEquals(text(99L, FP + 1, WORKERS), read(file(dir, "chkpt")));
		assertValues(settings.recover(), 99L, FP + 1, WORKERS);
		assertNoSettingsWarning();
	}

	@Test
	public void testFailedCommitKeepsPreviousSettings() throws Exception {
		final File dir = scratchDir();
		install(SEED, FP);
		final CheckpointSettings settings = new CheckpointSettings(dir.getAbsolutePath(), WORKERS);
		settings.beginChkpt();
		settings.commitChkpt();

		// No temporary sidecar is left to move, so this commit fails.
		try {
			settings.commitChkpt();
			fail("commit without a temporary sidecar must fail");
		} catch (IOException expected) {
			assertEquals(text(SEED, FP, WORKERS), read(file(dir, "chkpt")));
		}
	}

	@Test
	public void testRecoverDoesNotChangeRequestedSettings() throws Exception {
		final File dir = scratchDir();
		install(SEED, FP);
		final CheckpointSettings original = new CheckpointSettings(dir.getAbsolutePath(), WORKERS);
		original.beginChkpt();
		original.commitChkpt();
		final String committed = read(file(dir, "chkpt"));

		final long currentSeed = 7L;
		final int currentFp = FP + 1;
		final int currentWorkers = WORKERS + 2;
		install(currentSeed, currentFp);
		final CheckpointSettings current = new CheckpointSettings(dir.getAbsolutePath(), currentWorkers);
		final Values recovered = current.recover();

		assertValues(recovered, SEED, FP, WORKERS);
		assertEquals(currentSeed, RandomEnumerableValues.getSeed());
		assertEquals(FP64.Polys[currentFp], FP64.getIrredPoly());
		assertEquals(committed, read(file(dir, "chkpt")));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_MISMATCH,
				Long.toString(SEED), Integer.toString(FP), Integer.toString(WORKERS),
				Long.toString(FP64.Polys[FP]), Long.toString(currentSeed), Integer.toString(currentFp),
				Integer.toString(currentWorkers), Long.toString(FP64.Polys[currentFp]),
				"seed, fingerprint, workers"));
		assertFalse(recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_UNVERIFIABLE));
	}

	@Test
	public void testRecoverReadsTheRecoveryDirectory() throws Exception {
		final File written = scratchDir();
		final File other = scratchDir();
		install(SEED, FP);
		final CheckpointSettings checkpoint = new CheckpointSettings(written.getAbsolutePath(),
				other.getAbsolutePath(), WORKERS);
		checkpoint.beginChkpt();
		checkpoint.commitChkpt();

		assertNull(checkpoint.recover());
		assertNoSettingsWarning();
		assertTrue(file(written, "chkpt").isFile());
		assertFalse(file(other, "chkpt").exists());

		final CheckpointSettings sameDir = new CheckpointSettings(written.getAbsolutePath(), WORKERS);
		assertValues(sameDir.recover(), SEED, FP, WORKERS);
	}

	@Test
	public void testDifferentRevisionAndLegacyMetadata() throws Exception {
		final File dir = scratchDir();
		install(SEED, FP);
		final CheckpointSettings settings = new CheckpointSettings(dir.getAbsolutePath(), WORKERS);
		final String legacy = text(SEED, FP, WORKERS).split("revision=")[0];
		Files.write(file(dir, "chkpt").toPath(), legacy.getBytes(StandardCharsets.UTF_8));
		assertValues(settings.recover(), SEED, FP, WORKERS);
		assertFalse(recorder.recorded(EC.GENERAL));
		Files.write(file(dir, "chkpt").toPath(), (legacy + "revision=other-build\n").getBytes(StandardCharsets.UTF_8));
		assertValues(settings.recover(), SEED, FP, WORKERS);
		assertTrue(recorder.recorded(EC.GENERAL));
	}

	private void install(long seed, int fp) {
		if (recorder == null) {
			recorder = new TestMPRecorder();
			MP.setRecorder(recorder);
		}
		RandomEnumerableValues.setSeed(seed);
		FP64.Init(fp);
	}

	private void assertNoSettingsWarning() {
		assertFalse(recorder.recorded(EC.GENERAL));
		assertFalse(recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_MISMATCH));
		assertFalse(recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_UNVERIFIABLE));
	}

	private static void assertValues(Values values, long seed, int fp, int workers) {
		assertEquals(seed, values.seed);
		assertEquals(fp, values.fpIndex);
		assertEquals(FP64.Polys[fp], values.fp);
		assertEquals(workers, values.workers);
	}

	private static String text(long seed, int fp, int workers) {
		return "version=1\n"
				+ "seed=" + seed + "\n"
				+ "fpIndex=" + fp + "\n"
				+ "fp=" + FP64.Polys[fp] + "\n"
				+ "workers=" + workers + "\n"
				+ "revision=" + TLCGlobals.Version.revisionOrDev() + "\n";
	}

	private static String read(File file) throws Exception {
		return new String(Files.readAllBytes(file.toPath()), StandardCharsets.UTF_8);
	}

	private static File file(File dir, String ext) {
		return new File(dir, "settings." + ("tmp".equals(ext) ? "tmp.chkpt" : ext));
	}

	private File scratchDir() throws Exception {
		final File dir = Files.createTempDirectory("checkpoint-settings").toFile();
		scratch.add(dir);
		return dir;
	}
}
