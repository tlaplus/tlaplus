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
package tlc2.tool.fp;

import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;
import util.TLCRuntime;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import static org.junit.Assert.*;

public class LongArrayTest {

    @Before
    public void setup() {
        Assume.assumeTrue(TLCRuntime.getInstance().getArchitecture() == TLCRuntime.ARCH.x86_64);
    }

    @Test
    public void testGetAndSet() {
        final int elements = 100;

        final LongArray array = new LongArray(elements);
        array.zeroMemory();

        for (long i = 0L; i < elements; i++) {
            assertEquals(0L, array.get(i));
        }


        for (long i = 0L; i < elements; i++) {
            array.set(i, i);
        }
        for (long i = 0L; i < elements; i++) {
            assertEquals(i, array.get(i));
        }


        for (long i = 0L; i < elements; i++) {
            array.set(i, Long.MAX_VALUE - i);
        }
        for (long i = 0L; i < elements; i++) {
            assertEquals(Long.MAX_VALUE - i, array.get(i));
        }


        for (long i = 0L; i < elements; i++) {
            array.set(i, Long.MIN_VALUE + i);
        }
        for (long i = 0L; i < elements; i++) {
            assertEquals(Long.MIN_VALUE + i, array.get(i));
        }
    }

    @Test
    public void testOutOfRangePositive() {
        final LongArray array = new LongArray(1);
        try {
            array.get(1);
        } catch (final AssertionError e) {
            return;
        }
        fail();
    }

    @Test
    public void testOutOfRangeNegative() {
        final LongArray array = new LongArray(1);
        try {
            array.get(-1);
        } catch (final AssertionError e) {
            return;
        }
        fail();
    }

    @Test
    public void testGetAndTrySet() {
        final int elements = 100;

        final LongArray array = new LongArray(elements);
        array.zeroMemory();

        // Assert zero successful
        for (long i = 0L; i < elements; i++) {
            assertEquals(0L, array.get(i));
        }

        // trySet linear elements.
        for (long i = 0L; i < elements; i++) {
            assertTrue(array.trySet(i, 0, i));
        }
        for (long i = 0L; i < elements; i++) {
            assertEquals(i, array.get(i));
        }

        // Replace with largest possible values
        for (long i = 0L; i < elements; i++) {
            array.trySet(i, i, Long.MAX_VALUE - i);
        }
        for (long i = 0L; i < elements; i++) {
            assertEquals(Long.MAX_VALUE - i, array.get(i));
        }


        // Replace with smallest possible values
        for (long i = 0L; i < elements; i++) {
            array.trySet(i, Long.MAX_VALUE - i, Long.MIN_VALUE + i);
        }
        for (long i = 0L; i < elements; i++) {
            assertEquals(Long.MIN_VALUE + i, array.get(i));
        }
    }

    @Test
    public void testZeroMemory() {
        for (int k = 1; k < 8; k++) {
            for (int i = 1; i < 128; i++) {
                final LongArray array = new LongArray(i);
                array.zeroMemory(k);
                for (final int j = 0; i < j; i++) {
                    assertEquals(0L, array.get(j));
                }
            }
        }
    }

    @Test
    public void testSwap() {
        final int elements = 10321;

        final LongArray array = new LongArray(elements);
        array.zeroMemory();

        for (long i = 0L; i < elements; i++) {
            final long value = Long.MAX_VALUE - i;
            array.set(i, value);
        }

        for (int i = 0; i < (elements / 2); i++) {
            array.swapCopy(i, (elements - 1) - i);
        }

        for (long i = 0L; i < elements; i++) {
            assertEquals(Long.MAX_VALUE - (elements - 1) + i, array.get(i));
        }
    }

    @Test
    public void testSwapRandom() {
        final int elements = 21383;

        final List<Long> vals = new ArrayList<>();
        final Random rnd = new Random();

        for (int i = 0; i < elements; i++) {
            vals.add(rnd.nextLong());
        }

        final LongArray array = new LongArray(elements);
        array.zeroMemory();

        for (int i = 0; i < elements; i++) {
            array.set(i, vals.get(i));
        }

        for (int i = 0; i < (elements / 2); i++) {
            array.swapCopy(i, (elements - 1) - i);
        }

        Collections.reverse(vals);

        for (int i = 0; i < elements; i++) {
            assertEquals((long) vals.get(i), array.get(i));
        }
    }
}
