// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp.iterator;

import java.util.NoSuchElementException;

import tlc2.tool.fp.MSBDiskFPSet;

import junit.framework.TestCase;

public class TLCIteratorTest extends TestCase {

	private MSBDiskFPSet.TLCIterator itr;

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();
		itr = new MSBDiskFPSet.TLCIterator(getBuffer());
	}
	
	protected long[][] getBuffer() {
		final long[][] buff = new long[8][];
		buff[0] = getArray(8, 1, 8);
		buff[1] = getArray(8, 9, 6);
		buff[2] = null;
		buff[3] = null;
		buff[4] = getArray(8, 15, 3);
		buff[5] = null;
		buff[6] = getArray(8, 18, 4);
		buff[7] = null;
		return buff;
	}
	
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
	
	/**
	 * Test method for {@link tlc2.tool.fp.TLCIterator#next()}.
	 */
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

	public void testGetLastLowBound() {
		assertEquals(getLast() + 1, itr.getLast(getLast() + 1));
	}
	
	/*
	 * Use a smaller lower bound element than last in the buffer.
	 */
	public void testGetLastLowerBoundNoHit() {
		assertEquals(getLast(), itr.getLast(20));
	}

}
