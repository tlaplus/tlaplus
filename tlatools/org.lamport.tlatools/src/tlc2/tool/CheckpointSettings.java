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
package tlc2.tool;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStreamWriter;
import java.io.Writer;
import java.nio.ByteBuffer;
import java.nio.charset.CharacterCodingException;
import java.nio.charset.CodingErrorAction;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.util.FP64;
import tlc2.value.RandomEnumerableValues;

/**
 * Versioned sidecar written next to the other checkpoint files. Legacy
 * checkpoints simply do not have this file.
 */
public class CheckpointSettings {

	private static final int CHECKPOINT_SETTINGS_VERSION = 1;
	private static final String CHECKPOINT_SETTINGS_FILE = "settings.chkpt";
	private static final String CHECKPOINT_SETTINGS_TMP_FILE = "settings.tmp.chkpt";
	/** Larger than any settings file this version writes; anything bigger is not metadata. */
	private static final int CHECKPOINT_SETTINGS_MAX_BYTES = 4096;

	private final String metadir;
	private final String fromChkpt;
	private final int workers;

	public CheckpointSettings(String metadir, String fromChkpt, int workers) {
		this.metadir = metadir;
		this.fromChkpt = fromChkpt;
		this.workers = workers;
	}

	public CheckpointSettings(String directory, int workers) {
		this(directory, directory, workers);
	}

	/**
	 * Write the effective seed, fingerprint, and worker count to a temporary
	 * sidecar. {@link #commitChkpt()} publishes it.
	 */
	public void beginChkpt() throws IOException {
		final File tmp = new File(this.metadir, CHECKPOINT_SETTINGS_TMP_FILE);
		try (Writer writer = new OutputStreamWriter(new FileOutputStream(tmp), StandardCharsets.UTF_8)) {
			writer.write(checkpointSettingsText());
		} catch (IOException e) {
			if (!tmp.delete() && tmp.exists()) {
				tmp.deleteOnExit();
			}
			throw e;
		}
	}

	private String checkpointSettingsText() {
		final long poly = FP64.getIrredPoly();
		return "version=" + CHECKPOINT_SETTINGS_VERSION + "\n"
				+ "seed=" + RandomEnumerableValues.getSeed() + "\n"
				+ "fpIndex=" + fingerprintIndex(poly) + "\n"
				+ "fp=" + poly + "\n"
				+ "workers=" + this.workers + "\n"
				+ "revision=" + TLCGlobals.Version.revisionOrDev() + "\n";
	}

	public void commitChkpt() throws IOException {
		final File oldChkpt = new File(this.metadir, CHECKPOINT_SETTINGS_FILE);
		final File newChkpt = new File(this.metadir, CHECKPOINT_SETTINGS_TMP_FILE);
		if (oldChkpt.exists() && !oldChkpt.delete()) {
			throw new IOException("CheckpointSettings.commitChkpt: cannot delete " + oldChkpt);
		}
		if (!newChkpt.renameTo(oldChkpt)) {
			throw new IOException("CheckpointSettings.commitChkpt: cannot rename " + newChkpt + " to " + oldChkpt);
		}
	}

	/** @return the {@link FP64#Polys} index of {@code poly}, or -1 if it is not in the table */
	private static int fingerprintIndex(final long poly) {
		final long[] polys = FP64.Polys;
		for (int i = 0; i < polys.length; i++) {
			if (polys[i] == poly) {
				return i;
			}
		}
		return -1;
	}

	/**
	 * Compare the checkpoint sidecar to this run. A missing sidecar is a legacy
	 * checkpoint and is recovered unchanged. Unreadable or inconsistent metadata
	 * produces a warning and recovery continues with the requested settings.
	 * Genuine I/O failures propagate to the existing fatal recovery handling.
	 * @return the stored settings, or null when the sidecar is absent or could not be checked
	 */
	public Values recover() throws IOException {
		final File file = new File(this.fromChkpt, CHECKPOINT_SETTINGS_FILE);
		if (!file.isFile()) {
			return null;
		}
		final byte[] bytes = new byte[CHECKPOINT_SETTINGS_MAX_BYTES + 1];
		int byteLength = 0;
		try (InputStream input = Files.newInputStream(file.toPath())) {
			while (byteLength < bytes.length) {
				final int count = input.read(bytes, byteLength, bytes.length - byteLength);
				if (count == -1) {
					break;
				}
				byteLength += count;
			}
		} catch (NoSuchFileException e) {
			return null;
		}
		if (byteLength > CHECKPOINT_SETTINGS_MAX_BYTES) {
			warnUnverifiableCheckpointSettings("malformed");
			return null;
		}
		final String text;
		try {
			text = StandardCharsets.UTF_8.newDecoder()
					.onMalformedInput(CodingErrorAction.REPORT)
					.onUnmappableCharacter(CodingErrorAction.REPORT)
					.decode(ByteBuffer.wrap(bytes, 0, byteLength)).toString();
		} catch (CharacterCodingException e) {
			warnUnverifiableCheckpointSettings("malformed");
			return null;
		}
		final Values settings = parseCheckpointSettings(text, byteLength);
		if (settings == null) {
			return null;
		}
		warnIfCheckpointSettingsDiffer(settings);
		return settings;
	}

	private void warnUnverifiableCheckpointSettings(final String reason) {
		MP.printWarning(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_UNVERIFIABLE, reason);
	}

	/**
	 * @return parsed settings, or null when a warning was already emitted
	 */
	private Values parseCheckpointSettings(final String text, final int byteLength) {
		if (byteLength > CHECKPOINT_SETTINGS_MAX_BYTES) {
			warnUnverifiableCheckpointSettings("malformed");
			return null;
		}
		final String[] rawLines = text.split("\n", -1);
		int lineCount = rawLines.length;
		if (lineCount > 0 && rawLines[lineCount - 1].isEmpty()) {
			lineCount--;
		}
		if (lineCount < 5) {
			warnUnverifiableCheckpointSettings("truncated");
			return null;
		}
		if (lineCount > 6 || (lineCount == 6 && !rawLines[5].matches("revision=[^\\r\\n]+\\r?"))) {
			warnUnverifiableCheckpointSettings("malformed");
			return null;
		}
		final String[] lines = new String[5];
		for (int i = 0; i < lines.length; i++) {
			lines[i] = rawLines[i].endsWith("\r") ? rawLines[i].substring(0, rawLines[i].length() - 1) : rawLines[i];
		}
		final Integer version = parseSettingsField(lines[0], "version");
		if (version == null) {
			warnUnverifiableCheckpointSettings("malformed");
			return null;
		}
		if (version.intValue() != CHECKPOINT_SETTINGS_VERSION) {
			warnUnverifiableCheckpointSettings("unsupported version");
			return null;
		}
		final Long seed = parseSettingsLong(lines[1], "seed");
		final Integer fpIndex = parseSettingsField(lines[2], "fpIndex");
		final Long fp = parseSettingsLong(lines[3], "fp");
		final Integer parsedWorkers = parseSettingsField(lines[4], "workers");
		if (seed == null || fpIndex == null || fp == null || parsedWorkers == null) {
			warnUnverifiableCheckpointSettings("malformed");
			return null;
		}
		if (parsedWorkers.intValue() < 1) {
			warnUnverifiableCheckpointSettings("invalid workers");
			return null;
		}
		if (fpIndex.intValue() < 0 || fpIndex.intValue() >= FP64.Polys.length
				|| FP64.Polys[fpIndex.intValue()] != fp.longValue()) {
			warnUnverifiableCheckpointSettings("invalid fingerprint");
			return null;
		}
		if (lineCount == 6) {
			final String checkpointRevision = rawLines[5].trim().substring("revision=".length());
			final String currentRevision = TLCGlobals.Version.revisionOrDev();
			if (!checkpointRevision.equals(currentRevision)) {
				MP.printWarning(EC.TLC_CHECKPOINT_RECOVER_REVISION_MISMATCH,
						new String[] { checkpointRevision, currentRevision });
			}
		}
		return new Values(seed.longValue(), fpIndex.intValue(), fp.longValue(), parsedWorkers.intValue());
	}

	/** @return the integer value, or null when the line is not {@code key=integer} */
	private static Integer parseSettingsField(final String line, final String key) {
		final Long parsed = parseSettingsLong(line, key);
		if (parsed == null || parsed.longValue() < Integer.MIN_VALUE || parsed.longValue() > Integer.MAX_VALUE) {
			return null;
		}
		return Integer.valueOf(parsed.intValue());
	}

	/** @return the long value, or null when the line is not {@code key=long} */
	private static Long parseSettingsLong(final String line, final String key) {
		final String prefix = key + "=";
		if (!line.startsWith(prefix) || line.length() == prefix.length()) {
			return null;
		}
		try {
			return Long.valueOf(line.substring(prefix.length()));
		} catch (NumberFormatException e) {
			return null;
		}
	}

	private void warnIfCheckpointSettingsDiffer(final Values original) {
		final long currentPoly = FP64.getIrredPoly();
		final int currentFpIndex = fingerprintIndex(currentPoly);
		final long currentSeed = RandomEnumerableValues.getSeed();
		final int currentWorkers = this.workers;
		final StringBuilder changed = new StringBuilder();
		if (original.seed != currentSeed) {
			appendChangedSetting(changed, "seed");
		}
		if (original.fpIndex != currentFpIndex || original.fp != currentPoly) {
			appendChangedSetting(changed, "fingerprint");
		}
		if (original.workers != currentWorkers) {
			appendChangedSetting(changed, "workers");
		}
		if (changed.length() == 0) {
			return;
		}
		MP.printWarning(EC.TLC_CHECKPOINT_RECOVER_SETTINGS_MISMATCH, new String[] {
				Long.toString(original.seed),
				Integer.toString(original.fpIndex),
				Integer.toString(original.workers),
				Long.toString(original.fp),
				Long.toString(currentSeed),
				Integer.toString(currentFpIndex),
				Integer.toString(currentWorkers),
				Long.toString(currentPoly),
				changed.toString() });
	}

	private static void appendChangedSetting(final StringBuilder changed, final String name) {
		if (changed.length() > 0) {
			changed.append(", ");
		}
		changed.append(name);
	}

	public static final class Values {
		public final long seed;
		public final int fpIndex;
		public final long fp;
		public final int workers;

		Values(long seed, int fpIndex, long fp, int workers) {
			this.seed = seed;
			this.fpIndex = fpIndex;
			this.fp = fp;
			this.workers = workers;
		}
	}
}
