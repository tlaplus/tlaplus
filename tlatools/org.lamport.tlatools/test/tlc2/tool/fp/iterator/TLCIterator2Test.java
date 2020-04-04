// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp.iterator;

public class TLCIterator2Test extends TLCIteratorTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.iterator.TLCIteratorTest#getBuffer()
	 */
	@Override
	protected long[][] getBuffer() {
		final long[][] buff = new long[8][];
		buff[0] = getArray(8, 1, 8);
		buff[1] = getArray(8, 9, 6);
		buff[2] = null;
		buff[3] = null;
		
		buff[4] = getArray(8, 15, 7); // Bucket with last element
		buff[5] = null;
		
		// Simulate that this bucket is filled with fingerprints who have all
		// been flushed to disk.
		buff[6] = new long[4];
		buff[6][0] = 22L | 0x8000000000000000L;
		buff[6][1] = 0L;
		buff[6][2] = 0L;
		buff[6][3] = 0L;
		
		buff[7] = null;
		return buff;
	}
}
