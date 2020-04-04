package tlc2.tool.distributed;

import java.net.URI;
import java.rmi.RemoteException;

import tlc2.tool.TLCState;
import tlc2.tool.WorkerException;

/**
 * Poor mans RMI smart proxy which is used to measure network overhead
 */
public class TLCWorkerSmartProxy implements TLCWorkerRMI {

	/**
	 * The remote reference
	 */
	private final TLCWorkerRMI worker;
	/**
	 * Network overhead for a getNextStates method invocation
	 */
	private double networkOverhead = Double.MAX_VALUE;

	public TLCWorkerSmartProxy(final TLCWorkerRMI aWorker) {
		worker = aWorker;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#getNextStates(tlc2.tool.TLCState[])
	 */
	public NextStateResult getNextStates(final TLCState[] states) throws RemoteException, WorkerException {
		// Prefer currentTimeMillis over nanoTime as it uses less CPU cycles to read
		final long start = System.currentTimeMillis();
		
		// do actual remote call
		final NextStateResult nextStates = worker.getNextStates(states);

		final long roundTripTime = (System.currentTimeMillis() - start) + 1; // at least one millisecond if get next below resolution
		final long computationTime = sanitizeComputationTime(nextStates.getComputationTime());

		// RTT has to be bigger than computation alone
		double networkTime = Math.max(roundTripTime - computationTime, 0.00001d);

		double percentageNetworkOverhead = networkTime / roundTripTime;
		
		// network overhead per state
		networkOverhead = percentageNetworkOverhead / states.length;
		
		return nextStates;
	}
	
	// handle illegal values from worker
	private long sanitizeComputationTime(Long computationTime) {
		return Math.max(Math.abs(computationTime), 1);
	}

	/**
	 * @return The network overhead for a remote call in %
	 */
	public double getNetworkOverhead() {
		return networkOverhead;
	}
	
	/* All other methods just delegate */

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#exit()
	 */
	public void exit() throws RemoteException {
		worker.exit();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#getURI()
	 */
	public URI getURI() throws RemoteException {
		return worker.getURI();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#isAlive()
	 */
	public boolean isAlive() throws RemoteException {
		return worker.isAlive();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#getCacheRateRatio()
	 */
	public double getCacheRateRatio() throws RemoteException {
		return worker.getCacheRateRatio();
	}
}
