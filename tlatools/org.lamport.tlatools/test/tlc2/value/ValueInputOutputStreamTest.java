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
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.Test;

import tlc2.TLCGlobals;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import util.UniqueString;
import tlc2.tool.queue.DiskByteArrayQueue;

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

	private static interface WriteStringTestFns<Out extends IValueOutputStream, In extends IValueInputStream> {
		Out freshOutputStream() throws IOException;
		In getInputStream(Out out) throws IOException;
	}
	
	private <Out extends IValueOutputStream, In extends IValueInputStream> void writeStringTestImpl(WriteStringTestFns<Out, In> fns) throws IOException {
		final StringBuilder str16kBuilder = new StringBuilder();
		for(int i = 0; i < 16_000; i++) {
			final char ch = (char)((i % 26) + 'a');
			str16kBuilder.append(ch);
		}
		final StringBuilder str16kMultibyteBuilder = new StringBuilder();
		for(int i = 0; i < 16_000; i++) {
			if(i % 2 == 1) {
				str16kMultibyteBuilder.append("🗣️");
			} else {
				str16kMultibyteBuilder.append("🔥");
			}
		}
		
		final List<String> testStrings = Arrays.asList(
				// Short cases
				"",
				"foo",
				"ü",
				// <Null> character (surrounded by other chars to check it doesn't break things)
				"x\0x",
				// A really long repeating alphabet (good for debugging)
				str16kBuilder.toString(),
				// Short emoji sequence
				"🗣️🗣️🗣️🗣️🗣️🔥🔥🔥🔥🔥",
				// Very long emoji sequence
				str16kMultibyteBuilder.toString(),
				// Accent soup, maybe a different kind of stress test ("Zalgo text")
				"Z̴̢̳̫̤̥̗̻̙̦̘̣̞̝̝̫̫̭͓͛̒̂́̈́͋̔̏͊̃͂̒͜ä̷͈̯̜̬̹͓̩͇̠̙̼̰͓̤͔̱̞̹̹͈̺͔̏̃̅̽̂̂͌̓̏͂̈́̂̽̀́̎̕͜͝ͅḽ̸̛̞̣̜̭̱͎̮̳͙̃̾̉̂͗́̀̐͒̈̒͆̐̄̈̏̓̀͊̌̄̎͌͑́͑̋̂͒͒͌̓͝͝͝͝͝g̶̢̥͖̭̖͕̲̦͇̞͕̥͔̠̦̯͚͔̤̣̮̘̱͈͇̦͓̈́͒̄̅̇͗̾̈́̇͒̂̾̿̿̉̚͜͝ͅơ̸̻̠͙̼̼͚͖͖͙̲̠̹̹͓̣͋̾̇̿͌̓̾̆̾̍̈̀̉̂̓͆̉̃̀̿͗͑̂͆̋̿̑͘̚̚͘͠ͅͅ ̷̨̡̛̛̪͚̗̙̙̬̗̤̫͖̘̪̳̖͓͍̂͐̃̇͑̂́͆̎̃̃̏̈́̿̈́́̒̅͋̀̔͆̐̐̎̇͋̚͠͝͝͝͠͠ͅT̷̢̢̛͔̫̝̠̜͙͕͍̖͚͓̜̻̮͖̺̏͌̄̉̔͗́̓̉͐̀̇̾͆̿̅̔̅́̍͂̾̅͗̎̿́̕͝͠ȩ̶̗̲̦̤̻͓̥̯͍̦̐͌̔̈́͒̌͌̏̈́̌͌̉̆̾̀́̒̀͋̀͛͌̈́̈́̀͌̏̀̄̓́̑͌̒̍͊̚̚̕͜͜͝ͅx̵̡̡̡̡̢̡̛̤͖͙͖͉̬̥̹̖͔̱͕̞̩̟̹͔̦̣̦̗̫̺̜͍̻͈̃̓̇̓͑̽̅̎̓̌͑̂̇̔̒̇̄͐̅̌̓͋̄̕̚̚͠ţ̸̢̢̨̛̟͖̳̜̻̣̭̺͉̳̘̘̺͈͓̗̫̱͚̞̻͉̪͇̠̜͕͍͙͈̯͖̱̹͍̲̅̋͗̀̈́̓̈́͌̈́̆͑̽̓͌́̀̐̏͌͑̓͗̀͌̆̏͒̐̿̒̇̈͘͘͘͠͝͠ ̶̧̨̠̝̬̼͚̰̻̩͎̱̗͖͚̘͍̞̟̗̾͂͂́͑̓̑̽̐̽̌̂̀͘͝ͅͅĢ̸̧̛̻̳͚̈́̓̉́̎̓̀͛͒̌́̅̃̄̄͗́̋̈́̅͆͗̀̐̃̃̒̊̚͝͠e̸̢̢͈̬̮̥͎̠̫̘̎̄̐̍̈̿͌̇͌͘ͅn̴͈̹͙̊͋͒̈́̉̉̆̋́͌̐͆̀͆̐͆̊̊́̆̓̎̀͆̉͑̓̽̎̑̽̒͘͝͠͝͝ȩ̵̡̧̢̡̢̡͇̲̣͈̮̤̣͖͍̼͓̘̮͉͖͔̦̄̓̈́̓͒̈́̓̆̇̓͌̽͐͑̐́͛͋͊͑͊̅̀͜͜͝ͅͅŕ̶͙̠̞̯̺̠̞͚͕̥̮̝͖̝͒̆̈́̔̆͑͑̈́̀͒͗͛͘͜ͅa̸̱̪̩͚̝͉̖̰̹͎̠̐̿̃́̊̂̈̏̐̽̂̋̕͝t̸̘̗̯̜͆͋͒̾̋̂̓͌̑̋͗̋͛͂͌́̌̚͝ǫ̸̧̛̛̞̜͕͇̥̖̯̻͇͍̥͔̪͓͙͔̟̯̣̝͉͎̯͈͕̺͐͆̍̉̅̇̏̓͑̔̍̽̂̀͆̒̃̂̋̈́̈̈́͒̐͋͊͒̂͘̕͜͜͜͝͝͝͠ͅͅͅŕ̷̢̧̡̧̡̨̗̹̺̠̣̳͙͙͔͔̟̝̞̩͚̻̙̳̝͕͔̰̘͈̫̘̤̖̓̒̇̔͜͝ͅͅ ̶̢̲̘͇̼͙̖̥͇͖̼̙͉̹͎̗͚͖͉̇̆͂̀̓̔ͅͅi̴̧̡̯͖̝̺̥̟̞̤̫̳͉͙̫̼͔͍̤̼̼̊̆͋̈́̀̈́̃̾͌̓͗́̈̂̋̆͘s̵̢̧̢̡̗̬̟̳̹̘̠͉̜͖̻̫̹̻̼̙͖͈͕͖͎̪̖͉̗̜̥̩̺̜͔̮̥̙̰̑̀̋͒̈́͗̓͜ ̶̧̨̛̜̺̲͙̤̬͎̗̹͙͈̱̯͎̲͉̻͖̻̰̥̣͍̪̓̈́͋͑̎̀̊̆͂͊̀̅̐̌͘̕͠͝͝͠ͅą̶̡̨̛̼͇̞͈̰̗͓͇̤̲͈̲̙̩̹̩̙̰̼͎̗͚̳̗͓̞̪̫͓͇̔̈́̾͒̔̍́͋͌̂̀̀̀̄̓̉͂̎̍̎́̋̚̚͠͠ ̶̡̜̫͖̟̝͔͚̺͖͎͚̤̯͙̥͉̐̔̾̉̎̓̑̇̿̂̕̚͜͝f̶̡̨̧̛̖̜͖͚̤̥̼͕̭̥͕̼͔̭̳̫̹̞̯̫̅̈̎̀̿͋͐̽͊̋̂̀͂̑̑͗͌̾͊͗̇͒̌̊͂̚̚͝r̵̢̢̛͈̫̹̫̳̥̰̬̲̦̦̙̭͖̯͕͙̗̩͉̜̟̭̦̫̘͔͕̤͔̘̪̳̝̀̈́́̀̂͌̽͌̌̀͜͜͝ͅͅe̷̤̩̲͍͈͇̰̙͉͉̬̹̟͓̳̪͙͙̱͖͆͐̀̅͐̈́̒͝e̷̛͉̤͉͐̀̓̈́̂̂̇̀̉̏͂́́̒̔̄̍̈́́̀͛̿̽͆͒͑̀͌̑̚͠͝ ̵̩̺̟̹̰͋̆̐͑̀̈́͛͛̊ͅt̸̛̰̅̓̓̅ỏ̷͙̼͔͓͉̯͔̘̪͇͇̰͈̯̲̝͕̝̟̣̻̣͊͐͌͒̐̈́́̒̒͐͊̉̎̒̄̄̄̍̐͆̓́̃̈́́̄͘̕͠͠͠͝o̴̢̨̥̫̮͙̠̞̠̣͕̮͔̟̰̻̜͉͚̦̙̲̺̪̜̞̠̟͊̅̓͐̉̕͜͜͝ļ̵̡̨̛̦͖̘̰̼̞͎̘͉̩̳͈̫̰̟̈͛̑͂́̓̆̒̑̊͆̄̂̑̓͌͛̋͐̚͘͝ ̶̨̧̨̪̭̞̩̮͎̙̘͕̦̦̙̯̩̥͓͓̝̫͉̘̪̗̪͉̖̟̙̮̫͉̗͇̻̐̈́͛̆̈̌̆̈́̽̉͒̄̊̀͆͜͝͝ͅt̷̡̨̛̗̥̪̥̘̰̳͕̱̻̥̞͖͎̞͓͍̼̘̲̯̻̯̖͇͇͌̔͗́̃͋͆́̾̌̍́͋̇̊̑͂́̆̇́͐͒̄̑́͑̓̿̃̇̄͑̕̕͜͝͝ͅͅḩ̶̡̡̘̱̰̫͍͖̖̟͖̼͚̫̟̝͍͙̻̬̬̻̞̭̘̘̖̤̺̼͉͈̓̈́̾̓̈́ͅą̶̧̟͔͇̺͉͙̖̯̟͚̼̲̳̝͕̘̹̝͔̱̖̫͕̯̼̺̠̯͙̾̄̏͆t̶̛̟̏̃̎̌̐͌͑̈̎̂̓̌̉̏̋͌͋́̑̂̃̆̕͝͝͠ ̸̢̩̣̝͎͕͖̖̭̬̳̄͑̇̾̋̓̈́̽́̍̂́̄͐͊̈́͊̉̂̎̔̇̈́̏̋́̓̏̏̊͜͝͝͝͠͝͝͠ṭ̴̢̠͓̬̝̤̩̦̰͖̙̒̔̈́̈́͌̈͑̏̋͐̓̌̓͐̿̑̓͌́̌̈̓̇͌͊͒̃̉̌̋̑͘̚͠͝͠ṷ̶̧̧̨̨͓̫̟̰̜͉̜̲̱͖̬̬̞̪͖̙̘̰̤̖̞͎͐͜͜͜͝ͅͅr̷̢̧̡̩͖̘̝̺͙͕̳̯͙̳͕̠͓̼̫̱̼͖̙̝͈̂̋͐̔͆͐̊͛͐̈́͑͊͆͗̍͂̔̔͐̑͊͗͘̚͠͝͝͝͝͝͝n̴̢͎̪̲̮͍͚̖̩͙̤̖̥̝̝̱̹̬̖̦̘̖͙͍̹̲͖̲̹͓̩͍̠̑̒̄͐͛̆̕͘͜ͅs̷͍̹̫̣̬̣͐͂̔̀́̒̄͑͊̇̅͊͛̈́̌̋̇̅͊̔̕̚͘͜͜͝ͅ ̵̡̭̜̭̲͇̼̱͉͇̬̅̒̚͜ͅy̶̖̬͎̑̇̅̈̽̉̾̔̄̄͗̇͑̈́́͂͗̐͑̓͛̇͆̍͋͂̒͂̅͆̃͑̄̃̒̾̇̕͘͝o̶̧̱̝̮̲̰̫͙̻̯̙͙̮͗͐͌̀͊̽̀̿̏̑̏̈̒̾͗̐̔̀̿͐͂͘͠u̷̡͖̜͈̫̝̟̝̭͗̍̓̽͌͛r̵̡̡̛͉̟̪͙̳̹̳̘͕̻̘̯̻͙͚̪͖̱̞͔͚̤̤͔̱̽̈́̀͌͋͛͋͋̈́̉͜͝ͅ ̵̡̧̢̣̳̜̤̹͙̩̦͚͇̩̘̹̯̥̬͔͕͓͙̹̲͎̤̗̪̞̬̠̞̽͂̀̋̿̆̔̍͌͌̑͘͜͜n̷̡̛͎̣̭̳̟͔̠̖̩̼̜̈́̎̎̐̃̈̂̓̊͆̉͗̾̀̈́͂̽̕̕̕͜͝ơ̸̱̻͎̦̗͕̿̈̈́̋͛̓̀͊̔̍̓̆̓̃̄̇͒̾͌̉͊̈́͐̏̀̈̀̒͘͝͝r̵̨̧̛͔͙̬͕̩͙͎̤̹͉̣̹̘͔̠͕̟̻̘̟̹̂̌̈̽̔͊̾̈̉̉̆̐́͊̾͒̀̿̿̏̏͐̏̋́̏́̌́̽̄͑̎̃͘͝͝͝m̸̢̛̦͓͔̤͉̦̝͇̲͕̰̲͙̙̼̥̮͍̣͚̳͓̣̻̤͉̬̜̣͓̠̬̜̱̻̒̀̔͜͝a̴̛̬̦̰̟̟̙̭̲͈̱͎̦͋͋̃͌̈́̈́͗̋̌͆͑͒͊̉̉̃̆̂̔̍̓́͊͊̄̋̂̚̕͠ļ̸̢̤̤̣̜̩̮̗͕̗̼̩̹̙̩̜̟͖̖̰̜͖̣͖͎͔̪͎͓̖̙̀͒̈́̆̍̈͆́͑͌̕͜͠ ̶̨̧̖̣̣͉̩̼̤͓͕̲̜̰̲͔͓̘̊̑͌̈́̈͊̕͜t̵͓͔̬̦̼̬̪̹̱̮͚͔͈͕̮̘̲̆́̿͐̑͑̈́̇̇̑̕͘͜͠ͅȩ̵̢̡̧̛̩̠̪̦͎̦͉̭̹̮̭̜̭̞̖̮̤͍̗̰̤̭̘̟̖̩̞̗̬͈́̒͑̆͂͊̎̿́͋̿̄̈́͛̇̓̔̄̎̈͐̈́̅̚͜͝ͅx̷͈̻̟͎̘̠͚̘̖̗̩͍̼̝̹͍̫̪͙̖̣̦̮̯̤̣̮̩̫̱̣͓̖̗̞̏͊͌̒̊̃̅̊̋̔̔̇̑̅̓̎́̓̋̀̇̊̕͝ͅt̵̡̢̨̪̖̣͇̣̘̮̙̜̼̰͙̘̪̜̞̤͉̼̘̲͉̟̩̦̣̣̣̹̉̅̋́̒̈̃͐́͋̈́̊̒̄̈́͑̎̀͘͝͝ͅ ̷̢̮͖̫̝͕̥͈̭̹̰͖̞̗̰̗̳͔̠̌̿̔͐̀͑́́͠ï̴̧̛͈͇͎͎͙̳̤̜̂̓̎̇̄͑̐͐͑̈͛̀̓̈́̒̀́̓̿̀̾̀͒̍̐͒̈͆̚̚͘ń̴̡̡̨̛͇̰̰͖̳̤̲͖̺̖̮̃͂̆̀̌͗͂̏͒̊̌̊͊́̊̃͐̀̋̍̅̊̓͒̈́́͘͝͝͠ͅt̴̢̛̞̹̘̝͕̥̼̣̰͓̳̳̳̯͎́̌̓͂́̂̆͛̂͂̇͗̾̈́̄͒̈̆̇̏̈̐͆̚̚̕͘͝ờ̷͇̮̠̱͔̫̠̝̝̙̘̲͎̓͗͒̅͛͐̂́͊̊͑͘̚͘͘͜͝͝ ̴̡̡̛̛̙͈̜͔̯̻̻͚̗̖̖͓̪̗͍̫̠̗͍̜̯͙͕͗̆͊͌̓̇̀͒̃͌́͐̽͑͒͒̅̽̑̌̑̑̂͗̚͝͝͝͠c̷̛̮̥̰͔̱̬͗̆̐̇̽͊͆̈́̾̃̓͗͌̑̽̓̏̆̚͘͝r̶̢̧̛̘̮͚͓͍̤̟̭͖̳͕̣̻͚̜̦̰̮͖̼̖̭̹͍̖̣̠̲̪͕̱̘͙̗͉̃͂͆͑̓̅͐̉̀́͒̒̒̿̿̌͗̆̌̐̏̾̂̓͛̎̀̇̅̓́͘͜͜͝͝͠e̴̛̛̻͍͑̀̌̎̽͐͗̏̕͘̕e̶̢̫̯̳̟̪̩̪̥̥͈̭̪͓͎̝͕̙̬̹̲͉̭͕̔͐͊̉̃̊̾̏̉͌̓̈́̈̀̉̓̇̓͘͘͜ͅͅp̷̨̢̹͕͖̰̬̲̥̣̤̳̰̗͍̦͕͔̰̤̳̙̲͙͎̙̅̆̊̔͗͂̓̏̀̉̕̚͜͝͝ỷ̵̠͇̻̻̳͇̣̫̱̞̂͊̽͌͊̌̒̐͊̏͊̃̒̏̈́͂̋́̐͑̄͑̋̔ ̶̧̧̟̟̥̩̜̙̞̼̣͇͇̙͔̞͇͕̖͔̜̗̫̪͇̬͖̤̩̺̮̺̬͇̜̫̬̓͊̈̐͊̌̾̃̔̓͒͌̎̑̀̑͂̑̀̎͂̕̚͠͝ͅ(̸̧̲̹̙͚͖͍͓̻̠̤̯̮̻̫͕̱̥̝̮͚̞̞̽̌͐̈̓̌̐̾͑̂̀͒̀̒́̐̋̓͊́̽̕̕͘̕̕͘͠s̵̡̧̡̢͙͕͙͖͖͎̖̰̟͎͉̥̻̥̜̩̟͍̟̟̖̞͇̹̙̟̥̦͚̤̍̒̐͑̑͋ͅc̷̢̡̧̡̛̛̠̠̹̤͎̹͔͚͚͍̼̗̩͖̦̹̗̱̙̭̫̽̍̅̐̐̊̊͛̅̏͑̎͌͑͌̇̓̕à̵̧̡̧̧̢̢̡͇̻͉̯̯̱͈̻̯͕̥̙̭͙͔̱̦͔̖̤̳͚̗͙̝͓͚̙̈́r̷̨̧̧̨̢̯͕̰̩̹̯̼̲̦̗̩̝̪̭͍͇͍͍̣͔̦̳̟̠̍̔̽̐́̅͛̌̋̑͐̆͑̌̀̈́́̇̕͘͜ͅy̷̡̬̼͖̰̼̞͙̤͍̜̠̽̀̔̔̇̽̆̓̎̐́͌́͋̓́͒̆̋͒̇͋̎͆͆̀̈́͑̚͠͝͝)̷̜̼̪̞̤̭̲̘͓̍̅̅͑̅͑͂̍͂̄̇̅͑͒̒̿͋͑̒̋̀͆̓̊̄̀͑̽̂͗́̈́̕̚͘̕͜͠͝ ̴̢̡̥̞̱̪̭̹̱̞̘̞̱̺̬͉̰̣͓̯̉̄͌̒͋͜o̷̡̪̱͎̗̜͗̐͑͊̈́̒̇̒̾̌̐͑̓̀̂̀͂͑̎̎͆̈́̂́̄̚̚͜͝͝ŗ̴̢̡̧̨͎͎̣̪̹͉̹̮̠̼͔̬̫͚͓̺̱̼̟̗̘̮͈̦̟̤̰̟̮̮͍̣̎͂̒̅̓͌̕͜ ̷̡̨̨̛̩̭̥͕͇̯͓̼̺͖̰͍̲͖̘̬̤̖͓̯̠̩͚͈̹̭̞̰̲͚̼͈̠̖̑̑͋́̔͒͗̇̓͆̓͂̿́̔̔̆̍̄̇͐̓̋͛̔̕̕͘͜H̵̜̩̹̠͖͉̼̗͕̭̦̪͇̠̹͚̊̀͠͠ͅͅà̷̧̛̤̳̺̬͈͚͉̲͎͖͍̞͍͎͎̜̣̝̮̳̪̥̯̬̩̺̞̳͊̊͆̊̂̀̽́̄͜͜͜l̸̡̧͇̗̹̤̪̟̼̘̲͇̲̝͖̘͚͕̙̠͕̱͙̮̫͕̼̹̘̩̬͖͔̲̺̣̩̙̪̿̑̄̂͆͘͠ͅl̷̛̛͎̗̫̱̜̞̈́̄̅̔̒͑́̈́́̓͒́̾̔́̇̿̈́͒͋̄̑̒̌͑̊̀̂͌̍́̈́́́́͘̚͠o̶̡̡̲͍̼̗͔̦͚͕̣̯͔̟̦̖̲̤̖͎̘̖͉̻̗͖̅̾̆̉̅̅́́͌̐͊̃͑̈́̽̾͐̓̽̾́́͑͂̕̚̚̚͝͝ͅw̶̡͓̰̗̗͔̭͕̗̹͙͚̪͙͖͈͕̥̘̜̹̦͙̲̺̯͍̦͔̤͚̼͔̖͕̳̺̬̲͆̀̋͌̏̅̄̿͊̅̈́̊̿̇̉̈͗̅̊̇̏͂̾͘͜ę̸̱̫̘̘̯͚͙̠͋̐̿̑͗͊̈́̉͗̒̈̃̃̂̌͘͜͝͠ȩ̴̹̗̩̠̤̞̠̲͖̙͔͕̀͗̑̐̑͆͑̀͛̃͜ņ̵̨̧̧̛̰͕͖̦͕̮͚̜̱̲͕̭̈́̀̏̂̉͌̇͗͒̅͋̑͐̈́͋͆̅ ̸̢͙̲̦̮̂̋͌̑͐͌̒͂̏̋̂̾̈̈͆͋̋͒̋̐̅̓̀͗͜s̸̡̨̧̡̡̛̛̛͈̙̦̙̖̱̫͇̼̳̰̰̟̯͚̱̲͙̮̻͔͈̼̤̣̘͍͍̥̅̀̂͐̄̾͑̾͑͌̈́̇͗͗̍́̒͌̀̓̾͂̄̄̂͛͗̿͛͘͘͘̕͘͜͝t̶̨̧̨̡̧̡̢̢̛̞̺̲͚̟̘̫̫̺͎͚̯̫̬̥͚̙̪͇͛̇̏̍̌̂̊̽̌̂͂͋͗̈̓͊͌̾̑̽̈́̀͂̉̌̋͛̆̉͒̂̿͗̈̿͘͜͝ỳ̸̨̫̤̪̯͓̳̙̜̼͎͓͍̜̤̘͈̮̮̼̦̪̩̪͆̀̆͌̏̾̋͌̆̒͒̍́͆̈́̾̈̇͌̏̈́̎͐͊̾̉́̚͜͜͝͠l̵̙͖̐̈́̂͋̋̓̋́͝e̶̮͒̆̉̄͋̐̈́̓́̅́̎̅͆̕͠.̴̡̢̨̢̝̖͇̭̖͎̗͕͇͇͈̟͕̲̭̞͎̳̝̿͌͆̌̆͋̕̕͜͜"
		);
		
		final ArrayList<StringValue> testStringValues = new ArrayList<>();
		for(final String str : testStrings) {
			testStringValues.add(new StringValue(str));
		}
		
		// Note: for multibyte characters, behavior can sometimes vary depending
		//       on our alignment with buffer boundaries.
		//       This test has 2 versions offset by 1 byte relative to each other
		//       in the hopes of representing this scenario.
		for(final boolean causeMisalignment : new boolean[] { true, false } ) {
			for(final String str : testStrings) {
				final StringValue strVal = new StringValue(str);
				
				final var out = fns.freshOutputStream();
				if(causeMisalignment) {
					out.writeByte((byte)42);
				}
				strVal.write(out);
				out.close();
				
				final var in = fns.getInputStream(out);
				if(causeMisalignment) {
					assertEquals((byte)42, in.readByte());
				}
				assertEquals(str, strVal, in.read());
				// it would be bad if we only parsed a prefix of the stream
				assertTrue(in.atEOF());
				in.close();
			}
		}
	}
	
	@Test
	public void testWriteString() throws IOException {
		final File tempFile = File.createTempFile("ValueOutputStreamTest-testWriteString", ".vos");
		tempFile.deleteOnExit();
		writeStringTestImpl(new WriteStringTestFns<ValueOutputStream, ValueInputStream>() {
			@Override
			public ValueOutputStream freshOutputStream() throws IOException {
				return new ValueOutputStream(tempFile);
			}
			@Override
			public ValueInputStream getInputStream(ValueOutputStream out) throws IOException {
				return new ValueInputStream(tempFile);
			}
		});
	}
	
	@Test
	public void testWriteStringDiskByteArrayQueue() throws IOException {
		writeStringTestImpl(new WriteStringTestFns<DiskByteArrayQueue.ByteValueOutputStream, DiskByteArrayQueue.ByteValueInputStream>() {
			@Override
			public DiskByteArrayQueue.ByteValueOutputStream freshOutputStream() throws IOException {
				return new DiskByteArrayQueue.ByteValueOutputStream();
			}
			@Override
			public DiskByteArrayQueue.ByteValueInputStream getInputStream(DiskByteArrayQueue.ByteValueOutputStream out) throws IOException {
				return new DiskByteArrayQueue.ByteValueInputStream(out.toByteArray());
			}
		});
	}
}
