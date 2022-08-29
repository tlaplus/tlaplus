// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp.iterator;

import org.junit.Before;
import org.junit.Test;
import tlc2.tool.fp.MSBDiskFPSet;

import java.util.NoSuchElementException;

import static org.junit.Assert.*;

public class TLCIteratorTest {

    private MSBDiskFPSet.TLCIterator itr;

    /* (non-Javadoc)
     * @see junit.framework.TestCase#setUp()
     */
    @Before
    public void setUp() {
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

    protected long[] getArray(final int length, final long offset, final int numOfElements) {
        final long[] l = new long[length];
        for (int i = 0; i < length && i < numOfElements; i++) {
            l[i] = i + offset;
        }
        return l;
    }

    /**
     * Test method for {@link tlc2.tool.fp.MSBDiskFPSet.TLCIterator#next()}.
     */
    @Test
    public void testNext() {
        long predecessor = -1L;

        int i = 0;
        while (i < getLength()) {
            i++;
            assertTrue(itr.hasNext());

            final long next = itr.next();
            if (predecessor != -1L) {
                assertTrue(predecessor < next);
            }
            predecessor = next;
        }
        assertEquals(i, itr.reads());
    }

    /**
     * Test method for {@link tlc2.tool.fp.MSBDiskFPSet.TLCIterator#next()}.
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
        } catch (final NoSuchElementException e) {
            return;
        }
        fail("Must throw NoSuchElementException");
    }

    /**
     * Test method for {@link tlc2.tool.fp.MSBDiskFPSet.TLCIterator#getLast()}.
     */
    @Test
    public void testGetLast() {
        assertEquals(getLast(), itr.getLast());
    }
}
