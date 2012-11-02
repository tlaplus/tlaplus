package tlc2.tool.distributed;

import java.rmi.RemoteException;

import tlc2.tool.TLCState;
import tlc2.tool.WorkerException;
import tlc2.tool.distributed.selector.DummyTLCWorker;
import tlc2.tool.queue.DummyTLCState;
import junit.framework.TestCase;

public class TLCWorkerSmartProxyTest extends TestCase {

	private static final int ZERO = 0;
	private static final int ONE = 1;
	private static final int MAX_ARRAY_SIZE = Integer.MAX_VALUE * (1/10);
	
	public void testGetNetworkOverheadMaxStateOne() throws RemoteException, WorkerException {
		long calculationDuration = Long.MAX_VALUE;
		assertTrue(doTest(calculationDuration, new DummyTLCState[ONE]) > 0);
	}
	
	public void testGetNetworkOverheadMinStateOne() throws RemoteException, WorkerException {
		long calculationDuration = Long.MIN_VALUE;
		assertTrue(doTest(calculationDuration, new DummyTLCState[ONE]) > 0);
	}
	
	public void testGetNetworkOverheadZeroStateOne() throws RemoteException, WorkerException {
		long calculationDuration = ZERO;
		assertTrue(doTest(calculationDuration, new DummyTLCState[ONE]) > 0);
	}

	public void testGetNetworkOverheadMaxStateZero() throws RemoteException, WorkerException {
		long calculationDuration = Long.MAX_VALUE;
		assertTrue(doTest(calculationDuration, new DummyTLCState[ZERO]) > 0);
	}

	public void testGetNetworkOverheadMinStateZero() throws RemoteException, WorkerException {
		long calculationDuration = Long.MIN_VALUE;
		assertTrue(doTest(calculationDuration, new DummyTLCState[ZERO]) > 0);
	}

	public void testGetNetworkOverheadZeroStateZero() throws RemoteException, WorkerException {
		long calculationDuration = ZERO;
		assertTrue(doTest(calculationDuration, new DummyTLCState[ZERO]) > 0);
	}

	public void testGetNetworkOverheadMinStateMax() throws RemoteException, WorkerException {
		long calculationDuration = Long.MIN_VALUE;
		assertTrue(doTest(calculationDuration, new DummyTLCState[MAX_ARRAY_SIZE]) > 0);
	}

	public void testGetNetworkOverheadMaxStateMa() throws RemoteException, WorkerException {
		long calculationDuration = Long.MAX_VALUE;
		assertTrue(doTest(calculationDuration, new DummyTLCState[MAX_ARRAY_SIZE]) > 0);
	}

	public void testGetNetworkOverheadZeroStateMax() throws RemoteException, WorkerException {
		long calculationDuration = ZERO;
		assertTrue(doTest(calculationDuration, new DummyTLCState[MAX_ARRAY_SIZE]) > 0);
	}
	
	private double doTest(final long calculationDuration, final TLCState[] states) throws RemoteException, WorkerException {
		DummyTLCWorker aWorker = new DummyTLCWorker(calculationDuration);
		TLCWorkerSmartProxy proxy = new TLCWorkerSmartProxy(aWorker);

		// let proxy calculate current network overhead
		NextStateResult nsr = proxy.getNextStates(states);
		assertNotNull(nsr);

		double networkOverhead = proxy.getNetworkOverhead();
		return networkOverhead;
	}
}
