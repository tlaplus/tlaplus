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

import java.io.ByteArrayInputStream;
import java.io.EOFException;
import java.io.IOException;

import org.junit.Test;

import gov.nasa.jpf.util.test.TestJPF;
import gov.nasa.jpf.vm.Verify;

/**
 * Uses JPF to exhaustively verify
 * {@link BufferedDataInputStream#readString(int)} over all
 * {@code (streamLen, requestLen)} combinations in a bounded range.
 * <p>
 * The property under test: if {@code readString(requestLen)} returns normally
 * (without throwing {@link EOFException}), then the stream must have contained
 * at least {@code requestLen} bytes. Equivalently, if the stream has fewer
 * bytes than requested, the method <em>must</em> throw {@link EOFException}.
 * <p>
 * JPF's {@code Verify.getInt()} creates a choice generator that JPF explores
 * exhaustively. This finds the exact bug boundary: the double-counting
 * suppressed the {@link EOFException} whenever the available bytes {@code k}
 * satisfy {@code k >= requestLen/2}.
 * <p>
 * See <a href="https://github.com/tlaplus/tlaplus/issues/1154">#1154</a>.
 */
public class BufferedDataInputStreamJPFTest extends TestJPF {

	public static void main(String[] args) {
		new BufferedDataInputStreamJPFTest().testReadStringMustThrowOnShortStream();
	}

	/**
	 * JPF explores all 300 combinations of {@code streamLen ∈ [1,15]} and
	 * {@code requestLen ∈ [1,20]}. For each, it verifies that {@code readString}
	 * either returns a fully-populated string (when enough data exists) or throws
	 * {@link EOFException} (when not).
	 * <p>
	 * Historically, this test exposed a double-counting bug in
	 * {@link BufferedDataInputStream#readString(int)}: when the stream was shorter
	 * than requested but had at least half of the requested bytes, the method
	 * silently returned a NUL-padded string instead of throwing
	 * {@link EOFException}. It now serves as a regression test to guard against
	 * reintroducing that bug.
	 */
	@Test
	public void testReadStringMustThrowOnShortStream() {
		if (verifyNoPropertyViolation("+listener=.listener.AssertionProperty")) {
			try {
				int streamLen = Verify.getInt(1, 15);
				int requestLen = Verify.getInt(1, 20);

				byte[] data = new byte[streamLen];
				for (int i = 0; i < streamLen; i++) {
					data[i] = (byte) ('A' + (i % 26));
				}

				BufferedDataInputStream bdis = new BufferedDataInputStream(new ByteArrayInputStream(data));
				try {
					String result = bdis.readString(requestLen);

					// readString returned normally. This is only correct if the
					// stream had enough data.
					assert requestLen <= streamLen : "readString(" + requestLen + ") returned \"" + escape(result)
							+ "\" instead of throwing EOFException" + " (stream had only " + streamLen + " bytes)";

					// If the stream was long enough, every character must be valid.
					for (int i = 0; i < requestLen; i++) {
						assert result.charAt(i) == (char) ('A' + (i % 26)) : "readString(" + requestLen
								+ ") returned wrong char" + " at index " + i + ": expected '" + (char) ('A' + (i % 26))
								+ "', got '" + result.charAt(i) + "'";
					}
				} catch (EOFException e) {
					// EOFException is the correct behavior when requestLen > streamLen.
					assert requestLen > streamLen : "readString(" + requestLen + ") threw EOFException"
							+ " but stream had " + streamLen + " bytes (enough)";
				} finally {
					bdis.close();
				}
			} catch (IOException e) {
				assert false : "Unexpected IOException: " + e.getMessage();
			}
		}
	}

	private static String escape(String s) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < s.length(); i++) {
			char c = s.charAt(i);
			if (c == '\0') {
				sb.append("\\0");
			} else {
				sb.append(c);
			}
		}
		return sb.toString();
	}
}
