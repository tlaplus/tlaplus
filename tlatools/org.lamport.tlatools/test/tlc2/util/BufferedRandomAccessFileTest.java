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

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.OutputStreamWriter;

import org.junit.Assert;
import org.junit.Test;

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
			return;
		} catch (Exception e) {
			fail(e.getMessage());
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
	public void testReadSeek() throws IOException {
		final File tmpFile = File.createTempFile("BufferedRandomAccessFileTest_testReadSeek", ".bin");
		tmpFile.deleteOnExit();
		final java.io.RandomAccessFile raf = new BufferedRandomAccessFile(tmpFile, "rw");
		
		raf.setLength(BufferedRandomAccessFile.BuffSz + 1L);
		raf.seek(1);
		
		for (int i = 0; i < BufferedRandomAccessFile.BuffSz / 8; i++) {
			assertEquals(0L, raf.readLong());
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
			return;
		} catch (Exception e) {
			fail(e.getMessage());
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
}
