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
package tlc2.value;

import static org.junit.Assert.assertEquals;

import java.io.File;
import java.io.IOException;

import org.junit.Ignore;
import org.junit.Test;

import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.Value;
import util.UniqueString;

/**
 * A {@link RecordValue} with a non-ASCII field name does not survive a round
 * trip through {@link ValueOutputStream} and {@link ValueInputStream}, because
 * field names are written and read like strings. Records get such field names
 * from functions over strings, e.g. [a |-> 1] @@ [x \in {"café"} |-> 1], or
 * from deserialized JSON objects.
 * 
 * @see <a href="https://github.com/tlaplus/tlaplus/issues/1076">#1076</a>
 */
@Ignore("https://github.com/tlaplus/tlaplus/issues/1076")
public class UnicodeRecordValueSerializationTest {

	private static final String LATIN1 = "caf\u00e9";

	private static RecordValue record() {
		return new RecordValue(new UniqueString[] { UniqueString.uniqueStringOf("a"), UniqueString.uniqueStringOf(LATIN1) },
				new Value[] { IntValue.gen(1), IntValue.gen(2) }, false);
	}

	private static File write(final RecordValue value) throws IOException {
		final File tempFile = File.createTempFile("UnicodeRecordValueSerializationTest", ".vos");
		tempFile.deleteOnExit();
		final ValueOutputStream out = new ValueOutputStream(tempFile);
		value.write(out);
		out.close();
		return tempFile;
	}

	/**
	 * {@link ValueInputStream#read()} is the path of TLC's disk state queue. The
	 * restored field name keeps its token, so the record still equals the
	 * original, but the text of the field name differs.
	 */
	@Test
	public void testReadPreservesFieldName() throws IOException {
		final RecordValue original = record();
		final ValueInputStream in = new ValueInputStream(write(original));
		final RecordValue restored = (RecordValue) in.read();
		in.close();

		assertEquals(original, restored);
		assertEquals(LATIN1, restored.names[1].toString());
	}

	/**
	 * {@link ValueInputStream#readExternal()} is the path of IOUtils'
	 * IODeserialize. It re-interns the field names it read.
	 */
	@Test
	public void testReadExternalPreservesEquality() throws IOException {
		final RecordValue original = record();
		final ValueInputStream in = new ValueInputStream(write(original));
		final RecordValue restored = (RecordValue) in.readExternal();
		in.close();

		assertEquals(original, restored);
		assertEquals(LATIN1, restored.names[1].toString());
	}
}
