/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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

import java.util.NoSuchElementException;

import junit.framework.TestCase;

public class MemIntQueueTest extends TestCase {

	public void testDequeuePastLastElement() {
		final MemIntQueue queue = new MemIntQueue("irrelevant", "irrelevant");
		queue.enqueueInt(1);
		
		assertEquals(1, queue.dequeueInt());
		try {
			queue.dequeueInt();
		} catch (NoSuchElementException e) {
			return;
		}
		fail("Returned element where there should be none.");
	}
	
	// Add 0 three times and make sure it's only returned this many times. 0
	// is MemIntQueue's internal default for an empty slot.
	public void testEnqueueZeros() {
		final MemIntQueue queue = new MemIntQueue("irrelevant", "irrelevant");
		queue.enqueueInt(0);
		queue.enqueueInt(0);
		queue.enqueueInt(0);
		
		assertEquals(0, queue.dequeueInt());
		assertEquals(0, queue.dequeueInt());
		assertEquals(0, queue.dequeueInt());
		
		try {
			queue.dequeueInt();
		} catch (NoSuchElementException e) {
			return;
		}
		fail("Returned element where there should be none.");
	}
	
	public void testEnqueueLong() {
		final MemIntQueue queue = new MemIntQueue("irrelevant", "irrelevant");
		queue.enqueueLong(0);
		
		assertEquals(0, queue.dequeueInt());
		assertEquals(0, queue.dequeueInt());

		try {
			queue.dequeueInt();
		} catch (NoSuchElementException e) {
			return;
		}
		fail("Returned element where there should be none.");
	}
	
	public void testEnqueueDequeueLong() {
		final MemIntQueue queue = new MemIntQueue("irrelevant", "irrelevant");
		queue.enqueueLong(0);
		
		assertEquals(0, queue.dequeueLong());

		try {
			queue.dequeueLong();
		} catch (NoSuchElementException e) {
			return;
		}
		fail("Returned element where there should be none.");
	}
	
	public void testGrow() {
		final MemIntQueue queue = new MemIntQueue("irrelevant", "irrelevant", 4);
		queue.enqueueInt(0);
		queue.enqueueInt(1);
		queue.enqueueInt(2);
		queue.enqueueInt(3);
		assertEquals(4, queue.length());

		queue.dequeueInt();
		queue.dequeueInt();
		queue.dequeueInt();
		queue.dequeueInt();
		assertEquals(0, queue.length());

		queue.enqueueInt(4);
		queue.enqueueInt(5);
		queue.enqueueInt(6);
		queue.enqueueInt(7);
		assertEquals(4, queue.length());

		queue.dequeueInt();

		// This should make the queue grow internally.
		queue.enqueueInt(8);
		queue.enqueueInt(9);
		for(int i = 5; i < 10; i++) {
			assertEquals(i, queue.dequeueInt());
		}
		assertEquals(0, queue.length());
	}
}
