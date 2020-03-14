/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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
import java.io.IOException;

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
}
