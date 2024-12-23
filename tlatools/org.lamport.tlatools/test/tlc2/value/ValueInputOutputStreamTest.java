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
import java.nio.charset.StandardCharsets;

import org.junit.Test;

import tlc2.TLCGlobals;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import util.UniqueString;

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
	
	@Test
	public void testBlindReadStringValue() throws IOException {
		final File tempFile = File.createTempFile("ValueOutputStreamTest-testBlindReadStringValue", ".vos");
		tempFile.deleteOnExit();
		// Hopefully unused elsewhere in this codebase (meaning: fear of long words)
		final String str = "Hippopotomonstrosesquippedaliophobia";
		
		// Manually write out the bytes that make up a StringValue, bypassing the Value API entirely.
		// This is to be extra sure that we don't accidentally intern the string and make the test pass
		// when it shouldn't.
		final var out = new ValueOutputStream(tempFile);
		final byte[] strBytes = str.getBytes(StandardCharsets.UTF_8);
		// string value marker
		out.writeByte(Value.STRINGVALUE);
		// refs into the wrong TLC metadata (-1 for invalid)
		out.writeInt(-1);
		out.writeInt(-1);
		// length prefix (bytes in string)
		out.writeInt(strBytes.length);
		// the bytes
		out.getOutputStream().write(strBytes);
		out.close();
		
		// Now read the string, and assert that it was constructed correctly despite definitely
		// not already being in the intern table.
		final ValueInputStream in = new ValueInputStream(tempFile);
		final Value value = (Value)in.readExternal();
		assertEquals(Value.STRINGVALUE, value.getKind());
		final StringValue valueStr = (StringValue)value;
		assertEquals(UniqueString.uniqueStringOf(str), valueStr.getVal());
		assertEquals(str, valueStr.getVal().toString());
		in.close();
	}
	
	@Test
	public void testBlindReadRecordValue() throws IOException {
		// This test is like the one above, but it uses the string as a record key, which is a special case
		// and might invoke a different code path to direct string handling.
		final File tempFile = File.createTempFile("ValueOutputStreamTest-testBlindReadRecordValue", ".vos");
		tempFile.deleteOnExit();
		// Hopefully unused elsewhere in this codebase (snippet from famous Abbott and Costello comedy sketch)
		final String str = "Well, let's see, we have on the bags, Who's on first, What's on second, I Don't Know is on third";
		
		// Manually write out the bytes (see test case above).
		final var out = new ValueOutputStream(tempFile);
		final byte[] strBytes = str.getBytes(StandardCharsets.UTF_8);
		// record value marker
		out.writeByte(Value.RECORDVALUE);
		// number of key-value pairs
		out.writeInt(1);
		
		// --- key (the string)
		// byte marker, key is a string (not a DUMMYVALUE ref)
		out.writeByte(Value.STRINGVALUE);
		// refs into the wrong TLC metadata (-1 for invalid)
		out.writeInt(-1);
		out.writeInt(-1);
		// length prefix (bytes in string)
		out.writeInt(strBytes.length);
		// the bytes
		out.getOutputStream().write(strBytes);
		
		// --- value (int == 42)
		out.writeByte(Value.INTVALUE);
		out.writeInt(42);
		out.close();
		
		// Now read the record, and assert that its key was constructed correctly.
		final ValueInputStream in = new ValueInputStream(tempFile);
		final Value value = (Value)in.readExternal();
		assertEquals(Value.RECORDVALUE, value.getKind());
		final RecordValue valueRec = (RecordValue)value;
		assertEquals(1, valueRec.size());
		// check the contents... now we can make a StringValue, because we read the file already
		assertEquals(IntValue.gen(42), valueRec.select(new StringValue(str)));
		in.close();
	}
}
