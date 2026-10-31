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

import java.io.File;
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
	public void testDifferentRevision() throws Exception {
		final File dir = scratchDir();
		install(SEED, FP);
		final CheckpointSettings settings = new CheckpointSettings(dir.getAbsolutePath(), WORKERS + 1);
		write(file(dir, "chkpt"), withRevision(text(SEED, FP, WORKERS), "other-build"));
		assertNull(settings.recover());
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKPOINT_RECOVER_REVISION_MISMATCH,
				"other-build", TLCGlobals.Version.revisionOrDev()));
		// The other fields belong to the other revision's layout and are not compared.
		assertFalse(recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_MISMATCH));
		assertFalse(recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_UNVERIFIABLE));
	}

	@Test
	public void testDifferentRevisionIsReportedForUnparsableSettings() throws Exception {
		final File dir = scratchDir();
		install(SEED, FP);
		final CheckpointSettings settings = new CheckpointSettings(dir.getAbsolutePath(), WORKERS);
		write(file(dir, "chkpt"), "revision=other-build\nformat=from-the-future\n");
		assertNull(settings.recover());
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CHECKPOINT_RECOVER_REVISION_MISMATCH,
				"other-build", TLCGlobals.Version.revisionOrDev()));
		assertFalse(recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_UNVERIFIABLE));
	}

	@Test
	public void testRevisionIsMandatory() throws Exception {
		final File dir = scratchDir();
		install(SEED, FP);
		final CheckpointSettings settings = new CheckpointSettings(dir.getAbsolutePath(), WORKERS);
		final String withoutRevision = text(SEED, FP, WORKERS).substring(text(SEED, FP, WORKERS).indexOf('\n') + 1);

		write(file(dir, "chkpt"), "");
		assertNull(settings.recover());
		write(file(dir, "chkpt"), withoutRevision);
		assertNull(settings.recover());
		write(file(dir, "chkpt"), "revision=\n" + withoutRevision);
		assertNull(settings.recover());
		write(file(dir, "chkpt"), "revision=" + TLCGlobals.Version.revisionOrDev() + "\n");
		assertNull(settings.recover());

		final List<Object> records = recorder.getRecords(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_UNVERIFIABLE);
		assertEquals(4, records.size());
		assertEquals("truncated", ((String[]) records.get(0))[0]);
		assertEquals("malformed", ((String[]) records.get(1))[0]);
		assertEquals("malformed", ((String[]) records.get(2))[0]);
		assertEquals("truncated", ((String[]) records.get(3))[0]);
		assertFalse(recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_REVISION_MISMATCH));
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
		assertFalse(recorder.recorded(EC.TLC_CHECKPOINT_RECOVER_REVISION_MISMATCH));
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
		return "revision=" + TLCGlobals.Version.revisionOrDev() + "\n"
				+ "seed=" + seed + "\n"
				+ "fpIndex=" + fp + "\n"
				+ "fp=" + FP64.Polys[fp] + "\n"
				+ "workers=" + workers + "\n";
	}

	private static String read(File file) throws Exception {
		return new String(Files.readAllBytes(file.toPath()), StandardCharsets.UTF_8);
	}

	private static String withRevision(String text, String revision) {
		return "revision=" + revision + text.substring(text.indexOf('\n'));
	}

	private static void write(File file, String body) throws Exception {
		Files.write(file.toPath(), body.getBytes(StandardCharsets.UTF_8));
	}

	private static File file(File dir, String ext) {
		return new File(dir, "tmp".equals(ext) ? "settings.tmp.chkpt" : "settings.chkpt");
	}

	private File scratchDir() throws Exception {
		final File dir = Files.createTempDirectory("checkpoint-settings").toFile();
		scratch.add(dir);
		return dir;
	}
}
