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

import junit.framework.TestCase;

public class LongVecTest extends TestCase {

	protected LongVec getLongVec() {
		// default capacity
		return new LongVec();
	}
	
	public void testReadBeyondCapacity() {
		final LongVec vec = getLongVec();
		try {
			vec.elementAt(0);
		} catch (IndexOutOfBoundsException e) {
			return;
		}
		fail("Read beyond capacity");
	}

	public void testAddAndReadBeyondCapacity() {
		final LongVec vec = getLongVec();
		vec.addElement(1L);
		assertEquals(1L, vec.elementAt(0));
		try {
			vec.elementAt(1);
		} catch (IndexOutOfBoundsException e) {
			return;
		}
		fail("Read beyond capacity");
	}

	public void testRemoveBeyondCapacity() {
		final LongVec vec = new LongVec(10);
		for (int i = -1; i <= 10; i++) {
			try {
				vec.removeElement(0);
			} catch (IndexOutOfBoundsException e) {
				continue;
			}
			fail("Read beyond capacity");
		}
	}

	public void testAddRemoveBeyondCapacity() {
		final LongVec vec = new LongVec(10);
		vec.addElement(1L);
		vec.removeElement(0);
		try {
			vec.removeElement(1);
		} catch (IndexOutOfBoundsException e) {
			return;
		}
		fail("Read beyond capacity");
	}
	
	public void testRemoveAndGet() {
		final LongVec vec = getLongVec();
		vec.addElement(1L);
		vec.addElement(2L);
		vec.addElement(3L);
		
		assertEquals(1L, vec.elementAt(0));
		assertEquals(2L, vec.elementAt(1));
		assertEquals(3L, vec.elementAt(2));
		
		vec.removeElement(1);
		assertEquals(1L, vec.elementAt(0));
		assertEquals(3L, vec.elementAt(1));
		// There must not be an element at idx 2 anymore!
		try {
			vec.elementAt(2);
		} catch (IndexOutOfBoundsException e) {
			return;
		}
		fail("A new elements magically appeared in LongVec");
	}
	
	public void testRemoveWrongOrder() {
		final LongVec vec = getLongVec();
		vec.addElement(1L);
		vec.addElement(2L);
		
		assertEquals(1L, vec.elementAt(0));
		assertEquals(2L, vec.elementAt(1));
		
		vec.removeElement(0);
		try {
			vec.removeElement(1);
		} catch (IndexOutOfBoundsException e) {
			return;
		}
		fail("Removed non-existing element");
	}

	public void testGetNegative() {
		final LongVec vec = getLongVec();
		try {
			vec.elementAt(-1);
		} catch (IndexOutOfBoundsException e) {
			return;
		}
		fail("Read negative");
	}

	public void testRemoveNegative() {
		final LongVec vec = getLongVec();
		try {
			vec.removeElement(-1);
		} catch (IndexOutOfBoundsException e) {
			return;
		}
		fail("Removed negative");
	}
}
