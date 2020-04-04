/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved. 
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
package tlc2.value;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.IOException;

import org.junit.Test;

import tlc2.TLCGlobals;

public class ValueInputOutputStreamTest {

	@Test
	public void testWriteShort() throws IOException {
		final File tempFile = File.createTempFile("ValueOutputStreamTest-testWriteShort", ".vos");
		tempFile.deleteOnExit();
		
		final ValueOutputStream out = new ValueOutputStream(tempFile);
		out.writeShort(Short.MAX_VALUE);
		out.writeShort(Short.MIN_VALUE);
		out.writeShort((short) 0);
		out.close();
		
		final ValueInputStream in = new ValueInputStream(tempFile);
		assertEquals(Short.MAX_VALUE, in.readShort());
		assertEquals(Short.MIN_VALUE, in.readShort());
		assertEquals((short) 0, in.readShort());
		in.close();
	}

	@Test
	public void testWriteInt() throws IOException {
		final File tempFile = File.createTempFile("ValueOutputStreamTest-testWriteInt", ".vos");
		tempFile.deleteOnExit();
		
		final ValueOutputStream out = new ValueOutputStream(tempFile);
		out.writeInt(Integer.MAX_VALUE);
		out.writeInt(Integer.MIN_VALUE);
		out.writeInt(0);
		out.close();
		
		final ValueInputStream in = new ValueInputStream(tempFile);
		assertEquals(Integer.MAX_VALUE, in.readInt());
		assertEquals(Integer.MIN_VALUE, in.readInt());
		assertEquals(0, in.readInt());
		in.close();
	}

	@Test
	public void testWriteShortNat() throws IOException {
		final File tempFile = File.createTempFile("ValueOutputStreamTest-testWriteShortNat", ".vos");
		tempFile.deleteOnExit();
		
		TLCGlobals.useGZIP = true;
		final ValueOutputStream out = new ValueOutputStream(tempFile);
		out.writeShortNat(Short.MAX_VALUE);
		out.writeShortNat((short) 0);
		out.close();
		
		// 20 byte header
		// 2 byte Short.MAX_VALUE
		// 1 byte 0
		assertEquals(20 + 2 + 1, tempFile.length());
		
		final ValueInputStream in = new ValueInputStream(tempFile);
		assertEquals(Short.MAX_VALUE, in.readShortNat());
		assertEquals(0, in.readShortNat());
		in.close();
	}

	@Test
	public void testWriteNat() throws IOException {
		final File tempFile = File.createTempFile("ValueOutputStreamTest-testWriteNat", ".vos");
		tempFile.deleteOnExit();
		
		TLCGlobals.useGZIP = true;
		final ValueOutputStream out = new ValueOutputStream(tempFile);
		out.writeNat(Integer.MAX_VALUE);
		out.writeNat(0);
		out.close();
		
		// 20 byte header
		// 4 byte Integer.MAX_VALUE
		// 2 byte 0
		assertEquals(20 + 4 + 2, tempFile.length());
		
		final ValueInputStream in = new ValueInputStream(tempFile);
		assertEquals(Integer.MAX_VALUE, in.readNat());
		assertEquals(0, in.readNat());
		in.close();
	}
}
