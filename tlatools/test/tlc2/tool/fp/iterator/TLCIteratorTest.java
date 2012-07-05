// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp.iterator;

import java.util.NoSuchElementException;

import tlc2.tool.fp.TLCIterator;

import junit.framework.TestCase;

public abstract class TLCIteratorTest extends TestCase {

	private TLCIterator itr;

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();
		itr = new TLCIterator(getBuffer());
	}
	
	protected abstract long[][] getBuffer();
	
	protected long getLast() {
		return 21L;
	}
	
	protected int getLength() {
		return 21;
	}
	
	protected long[] getArray(int length, long offset, int numOfElements) {
		long[] l = new long[length];
		for (int i = 0; i < length && i < numOfElements; i++) {
			l[i] = i + offset;
		}
		return l;
	}

	/**
	 * Test method for {@link tlc2.tool.fp.TLCIterator#next()}.
	 */
	public void testNext() {
		long predecessor = -1l;
		
		int i = 0;
		while (i < getLength()) {
			i++;
			assertTrue(itr.hasNext());

			long next = itr.next();
			if (predecessor != -1l) {
				assertTrue(predecessor < next);
			}
			predecessor = next;
		}
		assertEquals(i, itr.reads());
	}
	
	public void testNoNext() {
		// read up all real elements
		while (itr.hasNext()) {
			itr.next();
		}
		
		// try to read further beyond end of itr
		assertFalse(itr.hasNext());
		try {
			itr.next();
		} catch (NoSuchElementException e) {
			return;
		}
		fail("Must throw NoSuchElementException");
	}
	
	/**
	 * Test method for {@link tlc2.tool.fp.TLCIterator#getLast()}.
	 */
	public void testGetLast() {
		assertEquals(getLast(), itr.getLast());
	}
}
