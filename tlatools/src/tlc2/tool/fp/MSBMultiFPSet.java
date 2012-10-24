// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.rmi.RemoteException;

@SuppressWarnings("serial")
public class MSBMultiFPSet extends MultiFPSet {

	private final int moveBy;

	public MSBMultiFPSet(final FPSetConfiguration fpSetConfiguration) throws RemoteException {
		super(fpSetConfiguration);
		
		this.moveBy = 63 - fpSetConfiguration.getFpBits();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.MultiFPSet#getNestedFPSets(int, long, int)
	 */
	protected FPSet[] getNestedFPSets(final FPSetConfiguration fpSetConfiguration) throws RemoteException {
		int len = fpSetConfiguration.getMultiFPSetCnt();
		final FPSet[] s = new FPSet[len];
		for (int i = 0; i < len; i++) {
			s[i] = FPSetFactory.getFPSet(new MultiFPSetConfiguration(fpSetConfiguration));
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
