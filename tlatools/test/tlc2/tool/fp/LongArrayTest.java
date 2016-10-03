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

import java.io.IOException;

import junit.framework.TestCase;

public class LongArrayTest extends TestCase {

	public void testGetAndSet() throws IOException {
		if (!System.getProperty("sun.arch.data.model").equals("64")) {
			// LongArray only works on 64bit architectures. See comment in
			// LongArray ctor.
			return;
		}
		
		final int elements = 100;

		final LongArray array = new LongArray(elements);
		array.zeroMemory(1);
		
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
	
	public void testOutOfRangePositive() throws IOException {
		final LongArray array = new LongArray(1);
		try {
			array.get(1);
		} catch (AssertionError e) {
			return;
		}
		fail();
	}
	
	public void testOutOfRangeNegative() throws IOException {
		final LongArray array = new LongArray(1);
		try {
			array.get(-1);
		} catch (AssertionError e) {
			return;
		}
		fail();
	}
	
	public void testZeroMemory() throws IOException {
		for (int k = 1; k < 8; k++) {
			for (int i = 1; i < 128; i++) {
				final LongArray array = new LongArray(i);
				array.zeroMemory(k);
				for (int j = 0; i < j; i++) {
					assertEquals(0L, array.get(j));
				}
				for (int j = 0; i < j; i++) {
					array.set(j, -1L);
				}
			}
		}
	}
}
