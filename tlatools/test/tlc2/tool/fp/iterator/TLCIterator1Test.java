// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp.iterator;

public class TLCIterator1Test extends TLCIteratorTest {

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.iterator.TLCIteratorTest#getBuffer()
	 */
	@Override
	protected long[][] getBuffer() {
		final long[][] buff = new long[8][];
		buff[0] = getArray(8, 1, 8);
		buff[1] = getArray(8, 9, 6);
		buff[2] = null;
		
		buff[3] = new long[4];
		buff[3][0] = -1;
		buff[3][1] = -1;
		buff[3][2] = -1;
		buff[3][3] = -1;
		
		buff[4] = getArray(8, 15, 3);
		buff[5] = null;
		buff[6] = getArray(8, 18, 4);
		buff[7] = null;
		return buff;
	}
}
