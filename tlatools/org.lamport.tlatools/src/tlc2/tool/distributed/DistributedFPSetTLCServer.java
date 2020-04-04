// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
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
	private final int expectedFPSetCount;

	public DistributedFPSetTLCServer(final TLCApp work, final int expectedFPSetCount) throws IOException,
			NotBoundException {
		super(work);
		this.expectedFPSetCount = expectedFPSetCount;
		this.latch = new CountDownLatch(expectedFPSetCount);
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServer#getFPSetManagerImpl(tlc2.tool.distributed.TLCApp, java.lang.String, int)
	 */
	protected IFPSetManager getFPSetManagerImpl(final TLCApp work,
			final String metadir, final int fpsetCount) throws IOException {
		return new DynamicFPSetManager(fpsetCount);
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
		MP.printMessage(EC.TLC_DISTRIBUTED_SERVER_FPSET_WAITING,
				Integer.toString(this.expectedFPSetCount));
		latch.await();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServer#registerFPSet(tlc2.tool.distributed.fp.FPSetRMI, java.lang.String)
	 */
	public synchronized void registerFPSet(FPSetRMI fpSet, String hostname) throws RemoteException {
		this.fpSetManager.register(fpSet, hostname);
		latch.countDown();
		
		long diff = this.expectedFPSetCount - latch.getCount();
		MP.printMessage(EC.TLC_DISTRIBUTED_SERVER_FPSET_REGISTERED,
				new String[] { Long.toString(diff),
				Integer.toString(this.expectedFPSetCount)});
	}
}
