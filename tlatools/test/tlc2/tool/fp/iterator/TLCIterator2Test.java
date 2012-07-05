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
		buff[4] = getArray(8, 15, 3);
		buff[5] = null;
		buff[6] = getArray(8, 18, 4);
		buff[7] = null;
		return buff;
	}
}
