// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.fp;

import java.rmi.RemoteException;

import tlc2.tool.fp.MemFPSet;

@SuppressWarnings("serial")
public class TestFPSet extends MemFPSet implements FPSetRMI {

	private int putInvocations = 0;
	private int containsInvocations = 0;

	protected TestFPSet() throws RemoteException {
		super();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.MemFPSet#put(long)
	 */
	public synchronized boolean put(long fp) {
		// Simulate network error after a single successful invocation
		if (putInvocations++ > 0) {
			throw new RuntimeException("Test FPSet");
		}
		return super.put(fp);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.MemFPSet#contains(long)
	 */
	public synchronized boolean contains(long fp) {
		// Simulate network error after a single successful invocation
		if (containsInvocations++ > 0) {
			throw new RuntimeException("Test FPSet");
		}
		return super.contains(fp);
	}
}
