// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp.iterator;

public class TLCIterator3Test extends TLCIteratorTest {
	
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
		buff[3][0] = -7737815633093123356L;
		buff[3][1] = -7737815243104283882L;
		buff[3][2] = -7737817099927946037L;
		buff[3][3] = -7737816871050596210L;
		
		buff[4] = new long[4];
		buff[4][0] = 1485563905028315074L;
		buff[4][1] = 1485571558183051350L;
		buff[4][2] = -7737800396242990929L;
		buff[4][3] = -7737808261470197641L;
		
		buff[5] = null;
		buff[6] = getArray(8, 1485571558183051351L, 4);
		buff[7] = null;
		return buff;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.iterator.TLCIteratorTest#getLast()
	 */
	@Override
	protected long getLast() {
		return 1485571558183051351L + 3L;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.iterator.TLCIteratorTest#getLength()
	 */
	@Override
	protected int getLength() {
		return 20;
	}
}
