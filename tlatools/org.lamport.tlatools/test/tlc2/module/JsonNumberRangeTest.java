/*******************************************************************************
 * Copyright (c) 2026 TLA+ Foundation. All rights reserved. 
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
package tlc2.module;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;

/**
 * Regression tests for https://github.com/tlaplus/tlaplus/issues/1502:
 * JSON numbers outside the 32-bit integer range must not be silently narrowed.
 */
public class JsonNumberRangeTest {

    @Rule
    public TemporaryFolder folder = new TemporaryFolder();

    private StringValue write(final String content) throws IOException {
        final File file = folder.newFile();
        Files.write(file.toPath(), content.getBytes(StandardCharsets.UTF_8));
        return new StringValue(file.getAbsolutePath());
    }

    @FunctionalInterface
    private interface Reader {
        void read(StringValue path) throws IOException;
    }

    private void assertRejected(final String content, final Reader reader) throws IOException {
        try {
            reader.read(write(content));
            fail("Expected rejection of: " + content);
        } catch (IOException e) {
            assertTrue(e.getMessage(), e.getMessage().contains("32-bit integer"));
        }
    }

    @Test
    public void plainInBounds() throws IOException {
        assertEquals(IntValue.gen(Integer.MAX_VALUE), Json.deserialize(write("2147483647")));
        assertEquals(IntValue.gen(Integer.MIN_VALUE), Json.deserialize(write("-2147483648")));
        assertEquals(IntValue.gen(1), Json.deserialize(write("1")));
    }

    @Test
    public void plainOutOfBounds() throws IOException {
        for (String n : new String[] {
                "4294967297", "2147483648", "-2147483649",
                "9007199254740993", "123456789012345678901234567890"
        }) {
            assertRejected(n, Json::deserialize);
        }
    }

    @Test
    public void nonInteger() throws IOException {
        for (String n : new String[] { "1.5", "-0.5", "0.1", "1.0", "1e-1", "1e2", "1E10", "[1,[2.5]]",
                "{\"a\":{\"b\":3.14}}" }) {
            assertRejected(n, Json::deserialize);
        }
        for (String n : new String[] { "1\n1.5\n", "{\"a\":0.25}\n", "[1]\n[2.0]\n" }) {
            assertRejected(n, Json::ndDeserialize);
        }
    }

    @Test
    public void nestedArray() throws IOException {
        final TupleValue v = (TupleValue) Json.deserialize(write("[1,[2147483647]]"));
        assertEquals(2, v.elems.length);

        assertRejected("[1,[4294967297]]", Json::deserialize);
    }

    @Test
    public void nestedObject() throws IOException {
        final RecordValue v = (RecordValue) Json.deserialize(write("{\"a\":{\"b\":-2147483648}}"));
        final RecordValue a = (RecordValue) v.select(new StringValue("a"));
        assertEquals(IntValue.gen(Integer.MIN_VALUE), a.select(new StringValue("b")));

        assertRejected("{\"a\":{\"b\":4294967297}}", Json::deserialize);
    }

    @Test
    public void ndJsonInBounds() throws IOException {
        final TupleValue v = (TupleValue) Json.ndDeserialize(write("1\n2147483647\n\n-2147483648\n"));
        assertEquals(3, v.elems.length);
        assertEquals(IntValue.gen(Integer.MAX_VALUE), v.elems[1]);
        assertEquals(IntValue.gen(Integer.MIN_VALUE), v.elems[2]);
    }

    @Test
    public void ndJsonOutOfBounds() throws IOException {
        for (String content : new String[] {
                "1\n4294967297\n",
                "{\"a\":1}\n{\"a\":2147483648}\n",
                "[1]\n[-2147483649]\n"
        }) {
            assertRejected(content, Json::ndDeserialize);
        }
    }
}
