// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp.iterator;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.util.NoSuchElementException;
import org.junit.Before;
import org.junit.Test;
import tlc2.tool.fp.MSBDiskFPSet;

public class TLCIteratorTest {

	private MSBDiskFPSet.TLCIterator itr;

	/* (non-Javadoc)
	 * @see junit.framework.TestCase#setUp()
	 */
	@Before
	public void setUp() throws Exception {
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
	@Test
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
	@Test
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
	@Test
	public void testGetLast() {
		assertEquals(getLast(), itr.getLast());
	}
}
