/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved.
 * Copyright (c) 2024, Oracle and/or its affiliates.
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
package tlc2.util;

import org.junit.Assert;
import org.junit.Test;

import java.io.File;
import java.io.IOException;

import static org.junit.Assert.assertEquals;

public class BufferedRandomAccessFileTest {

	@Test
	public void testWrite() throws IOException {
		final File tmpFile = File.createTempFile("BufferedRandomAccessFileTest_testWrite", ".bin");
		tmpFile.deleteOnExit();
		final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw");
		for (long i = 0L; i < BufferedRandomAccessFile.BuffSz / 8; i++) {
			raf.writeLong(i);
		}
		raf.close();
	}
	
	@Test
	public void testWriteSeek() throws IOException {
		final File tmpFile = File.createTempFile("BufferedRandomAccessFileTest_testWriteSeek", ".bin");
		tmpFile.deleteOnExit();
		final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw");
		
		raf.setLength(BufferedRandomAccessFile.BuffSz + 1L);
		raf.seek(1);
		
		for (long i = 0L; i < BufferedRandomAccessFile.BuffSz / 8; i++) {
			raf.writeLong(i);
		}
		raf.close();
	}
	
	@Test
	public void testWriteSeekNoLength() throws IOException {
		final File tmpFile = File.createTempFile("BufferedRandomAccessFileTest_testWriteSeekNoLength", ".bin");
		tmpFile.deleteOnExit();
		final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw");

		// Do not set length, expect meaningful exception
		raf.seek(1);
		try {
			for (long i = 0L; i < BufferedRandomAccessFile.BuffSz / 8; i++) {
				raf.writeLong(i);
			}
		} catch (IOException expected) {
			// OK!
		} finally {
			raf.close();
		}
	}
	
	@Test
	public void testRead() throws IOException {
		final File tmpFile = File.createTempFile("BufferedRandomAccessFileTest_testRead", ".bin");
		tmpFile.deleteOnExit();
		final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw");
		for (long i = 0L; i < BufferedRandomAccessFile.BuffSz / 8; i++) {
			raf.writeLong(i);
		}

		raf.seek(0);
		for (long i = 0l; i < BufferedRandomAccessFile.BuffSz / 8; i++) {
			assertEquals(i, raf.readLong());
		}
		raf.close();
	}

	@Test
	public void testReadSeekNoLength() throws IOException {
		final File tmpFile = File.createTempFile("BufferedRandomAccessFileTest_testReadSeekNoLength", ".bin");
		tmpFile.deleteOnExit();
		final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw");

		// Do not set length, expect meaningful exception
		raf.seek(1);
		try {
			for (int i = 0; i < BufferedRandomAccessFile.BuffSz / 8; i++) {
				raf.readLong();
			}
		} catch (IOException expected) {
			// OK!
		} finally {
			raf.close();
		}
	}

	@Test
	public void testInvalidateBufferedData() throws IOException {
		final File tmpFile = File.createTempFile("BufferedRandomAccessFileTest_testReadSeekNoLength", ".bin");
		tmpFile.deleteOnExit();

		try (BufferedRandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw")) {
			raf.write(new byte[]{ 1, 2, 3 });
			raf.flush();

			// these writes bypass raf's buffer
			try (BufferedRandomAccessFile other = new BufferedRandomAccessFile(tmpFile, "rw")) {
				other.write(new byte[] { 10, 20, 30 });
			}

			raf.seek(0);

			// data is buffered, so we don't see the new writes
			Assert.assertEquals(1, raf.read());
			Assert.assertEquals(2, raf.read());

			// invalidate the buffer --> now we see the new writes
			raf.invalidateBufferedData();
			Assert.assertEquals(30, raf.read());

			// indeed, we can see *all* of them
			raf.seek(0);
			Assert.assertEquals(10, raf.read());
			Assert.assertEquals(20, raf.read());
			Assert.assertEquals(30, raf.read());
		}
	}

	/**
	 * Create an empty file, call seek(1), then try to read.  The correct behavior is to return -1 for EOF.
	 * Earlier implementations of {@link BufferedRandomAccessFile} would incorrectly throw exceptions or return 0.
	 */
	@Test
	public void testReadAfterSeekPastEndOfFile() throws IOException {
		final File tmpFile = File.createTempFile("BufferedRandomAccessFileTest_testReadAfterSeekPastEndOfFile", ".bin");
		tmpFile.deleteOnExit();
		try (final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "r")) {
			raf.seek(1);

			assertEquals(1, raf.getFilePointer());

			int charRead = raf.read();
			assertEquals(-1, charRead);

			byte[] buffer = new byte[100];
			int nread = raf.read(buffer, 0, buffer.length);
			assertEquals(-1, nread);
		}
	}

	/**
	 * Create an empty file, call seek(10000), then try to write.  The correct behavior is to extend the length of
	 * the file and write the bytes.  Earlier implementations of {@link BufferedRandomAccessFile} would incorrectly
	 * throw exceptions.
	 */
	@Test
	public void testWriteAfterSeekPastEndOfFile() throws IOException {
		final File tmpFile = File.createTempFile("BufferedRandomAccessFileTest_testWriteAfterSeekPastEndOfFile", ".bin");
		tmpFile.deleteOnExit();
		try (final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw")) {
			raf.seek(10000);

			assertEquals(10000, raf.getFilePointer());

			byte[] buffer = new byte[100];
			raf.write(buffer);
			assertEquals(10000 + buffer.length, raf.length());
			assertEquals(10000 + buffer.length, raf.getFilePointer());
		}
	}

	/**
	 * While {@link java.io.RandomAccessFile} does not fully define how <code>setLength</code> changes the file pointer
	 * in some cases, our {@link BufferedRandomAccessFile} refinement does.  Specifically, the new pointer should be
	 * the minimum of the old pointer and the new length.
	 */
	@Test
	public void testObscureSetLengthBehavior() throws IOException {
		final File tmpFile = File.createTempFile("tmp", ".bin");
		tmpFile.deleteOnExit();
		try (final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw")) {
			raf.seek(200);
			Assert.assertEquals(200, raf.getFilePointer());

			raf.setLength(100);
			Assert.assertEquals(100, raf.getFilePointer());

			raf.setLength(300);
			Assert.assertEquals(100, raf.getFilePointer());
		}
	}

	/**
	 * All {@link java.io.Closeable} objects need to have an idempotent close method (although, confusingly, that
	 * requirement is documented in {@link AutoCloseable}).  Early versions of {@link BufferedRandomAccessFile}
	 * did not satisfy that property, and in particular they had a very nasty bug where duplicate close calls could
	 * cause two separate instances to share the same internal buffer array.
	 */
	@Test
	public void testIdempotentClose() throws IOException {
		final File f1 = File.createTempFile("tmp", ".bin");
		f1.deleteOnExit();

		final File f2 = File.createTempFile("tmp", ".bin");
		f2.deleteOnExit();

		try (BufferedRandomAccessFile raf = new BufferedRandomAccessFile(f1, "rw")) {
			raf.writeLong(100);
			raf.close(); // file will be closed again at the end of the try-block
		}

		try (BufferedRandomAccessFile raf1 = new BufferedRandomAccessFile(f1, "rw");
			 BufferedRandomAccessFile raf2 = new BufferedRandomAccessFile(f2, "rw")) {
			raf2.writeLong(200);
			Assert.assertEquals(100, raf1.readLong());
		}
	}

	/**
	 * Some (but not all) methods of {@link java.io.RandomAccessFile} are required to throw {@link IOException}
	 * if the file has been closed.  {@link BufferedRandomAccessFile} strengthens that contract: all of its
	 * read and write methods throw when the file is closed.
	 */
	@Test
	public void testIOExceptionOnUseAfterClose() throws IOException {
		final File tmpFile = File.createTempFile("tmp", ".bin");
		tmpFile.deleteOnExit();

		byte[] a = new byte[100];

		try (BufferedRandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw")) {
			raf.close();

			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.getFilePointer());
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.seek(0));
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.length());
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.setLength(100));
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.read());
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.read(a));
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.readInt());
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.readLong());
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.write(1));
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.write(a));
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.writeInt(100));
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.writeLong(100));
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.flush());
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.invalidateBufferedData());
			assertThrowsIOExceptionBecauseFileHandleClosed(() -> raf.reset());
		}
	}

	private void assertThrowsIOExceptionBecauseFileHandleClosed(IORunnable op) {
		try {
			op.run();
		} catch (IOException expected) {
			Assert.assertTrue(
					"Message must contain 'File handle closed', but was '" + expected.getMessage() + "'",
					expected.getMessage().contains("File handle closed"));
			return;
		} catch (Exception other) {
			throw new AssertionError("The operation threw a non-IOException", other);
		}
		throw new AssertionError("The operation did not throw anything");
	}

	private interface IORunnable {
		void run() throws IOException;
	}

	// ==============================================================================================================
	// The remaining tests were copied from fuzzer output (see BufferedRandomAccessFileFuzzTest).  They have cryptic
	// names and bodies because they were generated by a computer.
	//
	// These tests provide a quick litmus to catch problems we've had in the past with BufferedRandomAccessFile.  The
	// fact that these cases failed at some point during development indicates they are testing *something* that is
	// tricky to get right in the implementation.  Having them here guarantees that those tricky cases are covered
	// (the fuzz test is only probabilistic).
	//
	// While it is possible that some of these can be further simplified, there is not much benefit in doing so.
	// Changing them might make subtle changes to exactly which code paths in BufferedRandomAccessFile get covered.

	@Test
	public void regressionTest01() throws IOException {
		final File tmpFile = File.createTempFile("tmp", ".bin");
		tmpFile.deleteOnExit();
		try (final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw")) {
			raf.seek(98);
			raf.write(20);
			raf.write(43);
			raf.seek(98);
			Assert.assertEquals(20, raf.read());
		}
	}

	@Test
	public void regressionTest02() throws IOException {
		final File tmpFile = File.createTempFile("tmp", ".bin");
		tmpFile.deleteOnExit();
		try (final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw")) {
			raf.seek(98);
			raf.write(20);
			raf.write(43);
			raf.write(126);
			raf.seek(98);
			raf.read();
			raf.read();
			raf.write(123);
			Assert.assertEquals(-1, raf.read());
		}
	}

	@Test
	public void regressionTest03() throws IOException {
		final File tmpFile = File.createTempFile("tmp", ".bin");
		tmpFile.deleteOnExit();
		try (final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw")) {
			raf.seek(11624);
			Assert.assertEquals(0, raf.length());
		}
	}

	@Test
	public void regressionTest04() throws IOException {
		final File tmpFile = File.createTempFile("tmp", ".bin");
		tmpFile.deleteOnExit();
		try (final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw")) {
			raf.write(83);
			raf.seek(0);
			byte[] buffer = new byte[2];
			int n = raf.read(buffer, 0, 2);
			Assert.assertEquals(1, n);
			Assert.assertEquals(83, buffer[0]);
		}
	}

	@Test
	public void regressionTest05() throws IOException {
		final File tmpFile = File.createTempFile("tmp", ".bin");
		tmpFile.deleteOnExit();
		try (final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw")) {
			byte[] b1 = { 13, 41, -113, 61, -7 };
			raf.write(b1, 3, 1);
			raf.write(117);
			byte[] b2 = { 63, -59, 84, -4, 7 };
			raf.write(b2, 1, 1);
			raf.seek(2);

			// REMINDER: read() returns an UNSIGNED byte in the range [0, 255].  So even
			// though 197 does not appear in our writes, it is still the correct output
			// since it is the unsigned representation of the byte -59.
			Assert.assertEquals(197, raf.read());
		}
	}

	@Test
	public void regressionTest06() throws IOException {
		final File tmpFile = File.createTempFile("tmp", ".bin");
		tmpFile.deleteOnExit();
		try (final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw")) {
			raf.seek(9037);
			raf.setLength(8311);
			byte[] b1 = { 114, -128, 118, -15, -71, -43, -70, -27, 122, -33, -8, 80, -75, -7, -123, -88, -109, 4, 124, -69, 73, -86, 21, -63, 84, -13, 106, 81, 64, 69, -109, -56, -87, -48, 66, -98, -83, 44, 111, -77, 78, 17, -123, 115, -18, -55, -42, -75, 73, -73, -23, -125, -113, -39, 85, -39, -119, -16, 76, -106, -47, -72, 113, 25, 78, -90, 35, -2, -109, 1, 63, 43, 14, 44, -112, 8, -15, 15, 18, -82, -20, 13, 63, 86, -35, -92, -71, 85, 1, 82, 116, 29, 112, -53, -31, 10, 5, 37, 84, 96, -43, 2, -11, 10, 23, 50, -100, 72, -17, -124, -43, 14, -69, -98, 34, 119, 46, -30, -71, 45, 69, 31, -81, 60, 48, 37, 59, 15, 69, -91, -100, 125, 35, -43, 97, 106, -71, 24, -90, 26, -4, -117, 79, -89, 6, 46, -90, 52, 3, -2, 71, 121, 13, 14, 14, -82, 71, 82, -84, -31, -37, -6, 108, -84, -16, 23, -29, -125, -70, -78, -83, -23, -111, 10, -51, -51, -76, -36, 46, -70, -30, -57, 112, 34, -54, -108, -16, -5, -114, -93, -3, 109, 101, 11, -119, -102, -14, 121, 22, -112, -47, 106, 96, -6, 8, -47, -7, 42, -66, -90, -60, -50, -43, 78, -36, -10, 29, -51, -112, 26, 4, -97, -97, -84, -40, -76, 65, -82, -91, -35, 42, -56, 44, -50, 112, -12, 36, -109, -107, -120, -79, 49, 99, -123, -25, -51, -68, -79, 94, 38, 57, 81, 75, 0, -25, -70, -5, 3, 116, -74, -55, -115, -127, -34, -21, -26, 100, 122, -122, 112, -97, 71, 48, -21, 37, -128, -85, -88, -2, 86, 22, -24, -115, -16, 41, 73, -104, -47, -22, -70, -56, 125, -32, -127, -111, -63, -94, 102, -27, 121, 56, 13, 58, -32, 112, 119, 105, -24, -75, 119, -53, -64, -123, -124, -108, -42, 9, -30, 36, 30, -109, 39, -18, 42, -79, -78, 62, 73, -37, -96, -41, 85, 39, 58, -54, 19, -69, 111, 60, -89, 30, 37, -78, -112, 29, -69, 98, 108, 120, -54, 59, -19, 60, 74, -58, 20, -56, 126, 23, -125, -110, 85, -52, 42 };
			raf.write(b1, 196, 47);

			// Somewhat undocumented behavior: setLength will move file pointer if the file pointer is past the new
			// length.  This happens regardless of whether setLength extended or truncated the file.
			Assert.assertEquals(8358, raf.length());
		}
	}

	@Test
	public void regressionTest07() throws IOException {
		final File tmpFile = File.createTempFile("tmp", ".bin");
		tmpFile.deleteOnExit();
		try (final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw")) {
			raf.seek(9247);
			raf.setLength(1175);
			byte[] b1 = { 28, -61, -90, 105, -37, 115, 76, 15, -2, -82, -61, 66, -77, 73, -96, 119, 102, 8, 126, 40, -6, -80, 35, 112, 6, -9, -128, 72, 37, -20, 29, 119, -116, 110, 29, -83, -26, -63, 28, 79, -55, 75, 68, -44, -77, 13, 22, -58, 13, 5, 76, 88, 124, 104, -19, -87, -9, 121, -43, -83, 44, 84, 89, 39, 61, 60, -113, -46, -26, 56, 113, -121, 60, 90, -46, -70, 37, -95, 10, 18, 89, 21, 103, -77, 30, 10, -20, -23, 109, 81, -65, 7, 29, 96, -60, -88, -38, -65, -108, -127, -79, 106, -28, 63, -3, 31, -93, -74, -31, 18, 66, 37, 13, 56, -99, 2, -59, 29, -86, 33, -75, -76, 75, 61, 50, -64, -21, -122, -29, -70, -66, 8, 93, -28, 88, 40, -92, -10, 0, -11, -92, 40, 87, 40, 5, 35, -87, -86, -38, 22, 104, 113, 83, -70, 69, 32, -56, -27, -84, -78, 43, -125, -74, -84, -60, -46, -37, 99, 61, 86, -106, 56, -115, -41, 29, -28, -82, -111, 98, 17, -54, -64, 52, 2, 125, -118, 23, 65, -30, -125, 119, -102, 91, -71, -108, 75, 7, -73, -121, 58, -55, -81, 31, -85, -96, 76, -84, 66, -119, -29, 57, -126, -122, -69, -10, 124, -98, 97, -81, -23, -89, -97, 14, 12, 109, 79, -24, 38, 8, 43, 89, 108, -68, 23, -114, 112, 70, -123, 76, 72, -84, 10, 25, -46, 4, 8, 121, -59, -43, 98, 18, -114, -32, 48, 43, 26, 49, -33, 39, -68, -18, -75, 39, -21, -127, -64, -28, 74, -53, 119, -40, -62, 64, -54, 3, 44, -68, -92, -52, -80, 116, 58, -121, 108, 123, 82, -94, 106, -53, 80, -121, 16, -91, -80, 52, -106, -15, 68, 91, 125, -33, -53, 66, 124, 4, 69, 17, -127, 43, 58, -111, 70, -127, -112, -126, -86, 10, 3, -15, -125, 51, -47, 107, -70, 91, 58, 2, -82, -32, -62, -114, -92, 22, 35, 78, -45, -56, -37, -104, 15, 83, -41, -10, -68, 56, 75, -65, -10, 69, 117, 79, -21, -76, 24, -8, 63, 5, 61, 100, 27, -111, -59, -53, 104, 104, -15, -76, 59, -13, 91, -84, 86, 57, -66, -118, -57, -122, -95, 44, -100, -124, -16, -83, 38, 109, 1, 107, 23, -40, -127, -3, 80, 60, 0, -69, -58, -79, -27, 67, 77, -2, 125, 57, -108, 102, 64, 33, 1, -112, -3, -101, -4, 69, 65, 61, 0, -45, 109, 74, -77, -48, -43, -102, -126, -113, -40, -6, 41, 50, -30, -88, -73, -9, -77, 108, -99, 103, -85, 110, 49, 42, -81, 88, -99, -84, -71, 100, -69, 45, 127, -108, -119, 44, 62, 30, 42, 42, -63, 111, -68, 14, -123, -8, -90, -1, 71, 47, 122, 77, 69, 33, -17, 97, 110, 19, 75, -2, -63, 71, 69, 23, 28, 113, -14, -17, 60, -20, 85, 34, 100, 85, 28, -50, 64, 44, -29, -52, -54, -38, -83, 46, 89, -114, -89, -14, -83, -53, 93, 37, -7, 60, -51, -1, -58, 29, 16, 97, 37, 13, 9, 126, -99, 90, 34, -34, 4, 27, 59, 40, -46, 123, -128, -94, 83, 68, 101, -48, -67, -96, -48, 47, -27, -40, -101, -85, -60, 13, -81, -115, -128, 116, 9, -67, 69, 82, -128, 13, 118, -82, -103, 112, 7, 62, -19, 70, -17, 19, -57, -94, -67, -76, -76, -49, 51, 110, 113, -78, -110, 120, 50, -64, -127, 32, -43, 79, -52, 66, -56, 17, -73, 86, 122, 22, -122, -37, 19, 61, 113, 98, 121, 66, 95, -117, -127, -37, -118, 37, 47, -2, -83, -48, 46, 16, -117, 3, 27, 23, -94, -34, -38, 1, -63, -2, 79, 31, -118, 41, 44, -86, -11, -42, 43, 63, 121, -114, -24, -52, -24, 14, 16, 80, -87, -36, 72, -45, -63, -23, 0, -16, 115, -81, -45, -39, 75, 3, -40, -91, 110, 28, 4, 55, -52, -76, 109, 92, 105, -94, 28, 65, -107, -50, 65, -68, -109, 108, 77, 35, -77, -52, -77, 36, 53, 126, 72, -6, 70, -18, 64, 86, -4, -36, 1, -111, -28, 116, 19, 15, 71, -12, -15, 124 };
			raf.write(b1, 55, 500);
			raf.write(2);
			raf.setLength(71);
			raf.seek(1675);

			// Previous versions threw AssertionError on this call.
			raf.write(97);
		}
	}

}
