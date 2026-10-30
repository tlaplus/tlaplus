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
import static org.junit.Assert.assertSame;
import java.io.File;
import java.io.IOException;

import org.junit.BeforeClass;
import org.junit.Test;

import tlc2.value.ValueInputStream;
import tlc2.value.ValueOutputStream;
import tlc2.value.impl.ModelValue;
import util.Assert.TLCRuntimeException;

/**
 * @see <a href="https://github.com/tlaplus/tlaplus/issues/1500">#1500</a>
 */
public class ModelValueSerializationTest {

	private static final int[] INDICES = { 0, 1, 255, 256, Short.MAX_VALUE };

	@BeforeClass
	public static void setup() {
		ModelValue.init();
		for (int i = 0; i <= Short.MAX_VALUE; i++) {
			ModelValue.make("T_" + i);
		}
		ModelValue.setValues();
	}

	@Test(expected = TLCRuntimeException.class)
	public void testTooManyModelValues() {
		ModelValue.make("T_" + (Short.MAX_VALUE + 1));
	}

	@Test
	public void testByteValueStreamRoundTrip() throws IOException {
		for (final int i : INDICES) {
			final ModelValue original = ModelValue.mvs[i];
			assertEquals(i, original.index);

			final DiskByteArrayQueue.ByteValueOutputStream out = new DiskByteArrayQueue.ByteValueOutputStream();
			original.write(out);
			final byte[] bytes = out.toByteArray();
			assertEquals(3, bytes.length);

			assertSame(original, new DiskByteArrayQueue.ByteValueInputStream(bytes).read());
		}
	}

	@Test
	public void testValueStreamRoundTrip() throws IOException {
		final File tempFile = File.createTempFile("ModelValueSerializationTest", ".vos");
		tempFile.deleteOnExit();

		final ValueOutputStream out = new ValueOutputStream(tempFile);
		for (final int i : INDICES) {
			ModelValue.mvs[i].write(out);
		}
		out.close();

		ValueInputStream in = new ValueInputStream(tempFile);
		for (final int i : INDICES) {
			assertSame(ModelValue.mvs[i], in.read());
		}
		in.close();

		in = new ValueInputStream(tempFile);
		for (final int i : INDICES) {
			assertSame(ModelValue.mvs[i], in.readExternal());
		}
		in.close();
	}
}
