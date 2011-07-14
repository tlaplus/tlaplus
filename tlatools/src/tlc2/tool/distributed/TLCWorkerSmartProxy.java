package tlc2.tool.distributed;

import java.io.IOException;
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

	TLCWorkerSmartProxy(final TLCWorkerRMI aWorker) {
		worker = aWorker;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#getNextStates(tlc2.tool.TLCState[])
	 */
	public Object[] getNextStates(final TLCState[] states) throws RemoteException, WorkerException {
		final long start = System.currentTimeMillis();
		
		// do actual remote call
		final Object[] nextStates = worker.getNextStates(states);

		final long roundTripTime = System.currentTimeMillis() - start;
		final long computationTime = (Long) nextStates[2];
		networkOverhead = ((double) (roundTripTime - computationTime) / roundTripTime) / states.length;
		
		return nextStates;
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
	public void exit() throws IOException {
		worker.exit();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#getStatesComputed()
	 */
	public long getStatesComputed() throws RemoteException {
		return worker.getStatesComputed();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#getURI()
	 */
	public URI getURI() throws RemoteException {
		return worker.getURI();
	}
}
