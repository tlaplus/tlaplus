// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.rmi.RemoteException;

@SuppressWarnings("serial")
public class MSBMultiFPSet extends MultiFPSet {

	private final int moveBy;

	public MSBMultiFPSet(int bits, long fpMemSize) throws RemoteException {
		super(bits, fpMemSize);
		
		this.moveBy = 63 - bits;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.MultiFPSet#getNestedFPSets(int, long, int)
	 */
	protected FPSet[] getNestedFPSets(int bits, long fpMemSize, int len) throws RemoteException {
		final FPSet[] s = new FPSet[len];
		for (int i = 0; i < len; i++) {
			s[i] = FPSet.getFPSet(bits, (fpMemSize / (long) len), false);
		}
		return s;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.MultiFPSet#getFPSet(long)
	 */
	protected FPSet getFPSet(long fp) {
		long fp0 = fp & 0x7FFFFFFFFFFFFFFFL; // really zero msb?
		// determine corresponding fpset based on the msb bits
		final int idx = (int) (fp0 >> moveBy);
		return this.sets[idx];
	}
}
