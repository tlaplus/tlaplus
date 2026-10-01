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
package tlc2.tool.queue;

import static org.junit.Assert.assertEquals;

import java.io.IOException;

import org.junit.Ignore;
import org.junit.Test;

import tlc2.value.impl.StringValue;

/**
 * {@link DiskByteArrayQueue} has its own copy of the string serialization code
 * and the same defect as {@link util.BufferedDataInputStream}.
 * 
 * @see <a href="https://github.com/tlaplus/tlaplus/issues/1076">#1076</a>
 */
@Ignore("https://github.com/tlaplus/tlaplus/issues/1076")
public class DiskByteArrayQueueUnicodeTest {

	@Test
	public void testStringValueRoundTrip() throws IOException {
		final StringValue original = new StringValue("caf\u00e9");

		final DiskByteArrayQueue.ByteValueOutputStream out = new DiskByteArrayQueue.ByteValueOutputStream();
		original.write(out);

		final DiskByteArrayQueue.ByteValueInputStream in = new DiskByteArrayQueue.ByteValueInputStream(
				out.toByteArray());
		final StringValue restored = (StringValue) in.read();

		assertEquals(original, restored);
		assertEquals(original.getVal().toString(), restored.getVal().toString());
	}
}
