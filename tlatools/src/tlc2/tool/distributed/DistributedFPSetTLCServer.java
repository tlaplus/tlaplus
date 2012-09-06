// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.distributed;

import java.io.IOException;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.util.concurrent.CountDownLatch;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.distributed.fp.DynamicFPSetManager;
import tlc2.tool.distributed.fp.FPSetRMI;
import tlc2.tool.distributed.fp.IFPSetManager;

@SuppressWarnings("serial")
public class DistributedFPSetTLCServer extends TLCServer {
	
	protected final CountDownLatch latch;
	protected final IFPSetManager fpSetManager;

	public DistributedFPSetTLCServer(final TLCApp work, final int expectedFPSetCount) throws IOException,
			NotBoundException {
		super(work);

		this.fpSetManager = new DynamicFPSetManager(expectedFPSetCount);
		this.latch = new CountDownLatch(expectedFPSetCount);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServerRMI#getFPSetManager()
	 */
	public IFPSetManager getFPSetManager() {
		try {
			this.latch.await();
		} catch (InterruptedException e) {
			// not expected to happen
			MP.printError(EC.GENERAL, e);
		}
		return this.fpSetManager;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServer#waitForFPSetManager()
	 */
	protected void waitForFPSetManager() throws InterruptedException {
		latch.await();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServer#registerFPSet(tlc2.tool.distributed.fp.FPSetRMI, java.lang.String)
	 */
	public synchronized void registerFPSet(FPSetRMI fpSet, String hostname) throws RemoteException {
		this.fpSetManager.register(fpSet, hostname);
		latch.countDown();
	}
}
