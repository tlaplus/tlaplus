package tlc2.tool.distributed.selector;

import java.rmi.RemoteException;

import tlc2.tool.TLCState;
import tlc2.tool.WorkerException;
import tlc2.tool.distributed.TLCWorkerRMI;
import tlc2.tool.distributed.TLCWorkerSmartProxy;

public class DummyTLCWorker extends TLCWorkerSmartProxy implements TLCWorkerRMI {

	private long duration;

	public DummyTLCWorker(long duration) {
		super(null);
		this.duration = duration;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerSmartProxy#getNextStates(tlc2.tool.TLCState[])
	 */
	public Object[] getNextStates(TLCState[] states) throws RemoteException, WorkerException {
		Object[] res = new Object[3];
		res[2] = duration;
		return res;
	}
}
