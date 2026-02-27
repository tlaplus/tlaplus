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
import static org.junit.Assert.fail;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.EOFException;
import java.io.IOException;

import org.junit.Test;

public class BufferedDataInputStreamTest {

	/**
	 * {@code readString(n)} must throw {@link EOFException} when the stream
	 * contains fewer than {@code n} bytes.
	 * <p>
	 * This is a regression test for a former double-counting bug in
	 * {@link BufferedDataInputStream#readString(int)}: when the stream had at least
	 * {@code n/2} bytes, the method used to silently return a NUL-padded partial
	 * string instead of throwing.
	 * <p>
	 * See <a href="https://github.com/tlaplus/tlaplus/issues/1154">#1154</a>.
	 */
	@Test
	public void testReadStringThrowsOnShortStreamAtHalfBoundary() throws IOException {
		byte[] data = "ABCDEFGHIJ".getBytes(); // 10 bytes
		BufferedDataInputStream bdis = new BufferedDataInputStream(new ByteArrayInputStream(data));

		try {
			bdis.readString(15); // 10 >= 15/2, so the bug suppresses EOFException
			fail("readString(15) should throw EOFException when stream has only 10 bytes");
		} catch (EOFException expected) {
		} finally {
			bdis.close();
		}
	}

	/**
	 * {@code readString(n)} must throw {@link EOFException} when the stream
	 * contains fewer than {@code n} bytes, even when fewer than half are available.
	 * (This case is not affected by the double-counting bug because the
	 * double-counted {@code n} remains positive.)
	 */
	@Test
	public void testReadStringThrowsOnShortStreamBelowHalfBoundary() throws IOException {
		byte[] data = "AB".getBytes(); // 2 bytes
		BufferedDataInputStream bdis = new BufferedDataInputStream(new ByteArrayInputStream(data));

		try {
			bdis.readString(10); // 2 < 10/2, so EOFException is thrown despite the bug
			fail("readString(10) should throw EOFException when stream has only 2 bytes");
		} catch (EOFException expected) {
		} finally {
			bdis.close();
		}
	}

	/**
	 * Boundary case: requesting exactly as many bytes as available should work (the
	 * string is fully read before the refill returns EOF).
	 */
	@Test
	public void testReadStringExactLength() throws IOException {
		byte[] data = "ABCDEFGHIJ".getBytes();
		BufferedDataInputStream bdis = new BufferedDataInputStream(new ByteArrayInputStream(data));

		String result = bdis.readString(10);
		assertEquals("ABCDEFGHIJ", result);

		bdis.close();
	}

	/**
	 * Normal case: reading a string that spans an internal buffer refill, with
	 * sufficient data in the underlying stream. This should work regardless of the
	 * double-counting bug (because {@code n} reaches 0 in the inner loop).
	 */
	@Test
	public void testReadStringAcrossBufferRefill() throws IOException {
		// BufferedDataInputStream uses an 8192-byte internal buffer.
		// Write 8192 + 100 bytes so the string read spans a refill.
		byte[] data = new byte[8292];
		for (int i = 0; i < data.length; i++) {
			data[i] = (byte) ('A' + (i % 26));
		}
		BufferedDataInputStream bdis = new BufferedDataInputStream(new ByteArrayInputStream(data));

		// Advance past 8190 bytes so only 2 bytes remain in the buffer.
		bdis.readFully(new byte[8190], 0, 8190);

		// Read 10 chars: 2 from current buffer, refill, then 8 from new buffer.
		String result = bdis.readString(10);

		assertEquals("ABCDEFGHIJ", result);

		bdis.close();
	}

	/**
	 * Round-trip test using {@link BufferedDataOutputStream#writeString} and
	 * {@link BufferedDataInputStream#readString} via the {@code writeAnyString} /
	 * {@code readString} protocol used by UniqueString serialization.
	 */
	@Test
	public void testWriteReadStringRoundTrip() throws IOException {
		String original = "Hello, TLA+!";

		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		BufferedDataOutputStream bdos = new BufferedDataOutputStream(baos);
		bdos.writeInt(original.length());
		bdos.writeString(original);
		bdos.writeInt(42); // sentinel value after the string
		bdos.close();

		BufferedDataInputStream bdis = new BufferedDataInputStream(new ByteArrayInputStream(baos.toByteArray()));

		int len = bdis.readInt();
		String result = bdis.readString(len);
		assertEquals(original, result);

		int sentinel = bdis.readInt();
		assertEquals(42, sentinel);

		bdis.close();
	}
}
