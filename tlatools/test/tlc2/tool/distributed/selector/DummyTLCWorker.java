package tlc2.tool.distributed.selector;

import java.rmi.RemoteException;

import tlc2.tool.TLCState;
import tlc2.tool.TLCStateVec;
import tlc2.tool.WorkerException;
import tlc2.tool.distributed.NextStateResult;
import tlc2.tool.distributed.TLCWorkerRMI;
import tlc2.tool.distributed.TLCWorkerSmartProxy;
import tlc2.util.LongVec;

public class DummyTLCWorker extends TLCWorkerSmartProxy implements TLCWorkerRMI {

	private long duration;

	public DummyTLCWorker(long duration) {
		super(null);
		this.duration = duration;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerSmartProxy#getNextStates(tlc2.tool.TLCState[])
	 */
	public NextStateResult getNextStates(TLCState[] states) throws RemoteException, WorkerException {
		return new NextStateResult((TLCStateVec[]) null, (LongVec[]) null, duration, -1L);
	}
}
