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
package util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertSame;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;

import org.junit.Ignore;
import org.junit.Test;

/**
 * Non-ASCII strings do not survive a round trip through
 * {@link BufferedDataOutputStream#writeString(String)} and
 * {@link BufferedDataInputStream#readString(int)}: the writer keeps only the low
 * byte of each char, and the reader sign-extends each byte back into a char.
 * Thus, U+00E9 comes back as U+FFE9, and U+03BB as U+FFBB.
 * 
 * @see <a href="https://github.com/tlaplus/tlaplus/issues/1076">#1076</a>
 */
@Ignore("https://github.com/tlaplus/tlaplus/issues/1076")
public class UnicodeStringSerializationTest {

	// Escapes keep this file independent of the encoding javac assumes.
	private static final String LATIN1 = "caf\u00e9";
	private static final String BEYOND_LATIN1 = "\u03bb-calculus";

	private static String roundTrip(final String original) throws IOException {
		final ByteArrayOutputStream baos = new ByteArrayOutputStream();
		final BufferedDataOutputStream bdos = new BufferedDataOutputStream(baos);
		bdos.writeInt(original.length());
		bdos.writeString(original);
		bdos.writeInt(42); // sentinel value after the string
		bdos.close();

		final BufferedDataInputStream bdis = new BufferedDataInputStream(
				new ByteArrayInputStream(baos.toByteArray()));
		final String result = bdis.readString(bdis.readInt());
		assertEquals(42, bdis.readInt());
		bdis.close();
		return result;
	}

	@Test
	public void testBufferedDataStreamRoundTripLatin1() throws IOException {
		assertEquals(LATIN1, roundTrip(LATIN1));
	}

	@Test
	public void testBufferedDataStreamRoundTripBeyondLatin1() throws IOException {
		assertEquals(BEYOND_LATIN1, roundTrip(BEYOND_LATIN1));
	}

	/**
	 * {@link UniqueString#read(IDataInputStream)} is how the disk state queue
	 * restores the strings in states. It keeps the token from the stream, so the
	 * restored string still compares equal to the original, but its text (and
	 * thus the fingerprint of any value containing it) differs.
	 */
	@Test
	public void testUniqueStringReadRoundTrip() throws IOException {
		final UniqueString original = UniqueString.uniqueStringOf(LATIN1);

		final ByteArrayOutputStream baos = new ByteArrayOutputStream();
		final BufferedDataOutputStream bdos = new BufferedDataOutputStream(baos);
		original.write(bdos);
		bdos.close();

		final BufferedDataInputStream bdis = new BufferedDataInputStream(
				new ByteArrayInputStream(baos.toByteArray()));
		final UniqueString restored = UniqueString.read(bdis);
		bdis.close();

		assertEquals(original.getTok(), restored.getTok());
		assertEquals(LATIN1, restored.toString());
	}

	/**
	 * {@link UniqueString#readExternal(IDataInputStream)} is how IOUtils'
	 * IODeserialize restores strings. It re-interns the text it read, so a garbled
	 * text yields a different UniqueString than the original.
	 */
	@Test
	public void testUniqueStringReadExternalRoundTrip() throws IOException {
		final UniqueString original = UniqueString.uniqueStringOf(LATIN1);

		final ByteArrayOutputStream baos = new ByteArrayOutputStream();
		final BufferedDataOutputStream bdos = new BufferedDataOutputStream(baos);
		original.write(bdos);
		bdos.close();

		final BufferedDataInputStream bdis = new BufferedDataInputStream(
				new ByteArrayInputStream(baos.toByteArray()));
		final UniqueString restored = UniqueString.readExternal(bdis);
		bdis.close();

		assertSame(original, restored);
	}

	/**
	 * Recovering the intern table from a checkpoint must restore non-ASCII strings
	 * such that interning the same string again yields the token it had before the
	 * checkpoint. Otherwise, a string has two tokens after recovery.
	 */
	@Test
	public void testInternTableCheckpointRecovery() throws IOException {
		final File dir = Files.createTempDirectory("InternTableChkpt").toFile();
		dir.deleteOnExit();

		final InternTable beforeChkpt = new InternTable(16);
		final UniqueString original = beforeChkpt.put(LATIN1);
		beforeChkpt.beginChkpt(dir.getAbsolutePath());
		beforeChkpt.commitChkpt(dir.getAbsolutePath());
		new File(dir, "vars.chkpt").deleteOnExit();

		final InternTable afterChkpt = new InternTable(16);
		afterChkpt.recover(dir.getAbsolutePath());

		assertNotNull(afterChkpt.find(LATIN1));
		assertEquals(original.getTok(), afterChkpt.put(LATIN1).getTok());
	}
}
