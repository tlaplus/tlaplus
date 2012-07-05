// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.util.NoSuchElementException;

import junit.framework.TestCase;

public class TLCIteratorTest extends TestCase {

	private TLCIterator itr;

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	protected void setUp() throws Exception {
		super.setUp();

		final long[][] buff = new long[8][];
		buff[0] = getArray(8, 1, 8);
		buff[1] = getArray(8, 9, 6);
		buff[2] = null;
		buff[3] = null;
		buff[4] = getArray(8, 15, 3);
		buff[5] = null;
		buff[6] = getArray(8, 18, 4);
		buff[7] = null;
		
		itr = new TLCIterator(buff);
	}
	
	private long[] getArray(int length, long offset, int numOfElements) {
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
		while (i < 21) {
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
		assertEquals(21, itr.getLast());
	}
}
