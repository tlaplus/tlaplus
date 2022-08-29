package tlc2.tool.distributed.selector;

import tlc2.tool.TLCState;
import tlc2.tool.distributed.NextStateResult;
import tlc2.tool.distributed.TLCWorkerRMI;
import tlc2.tool.distributed.TLCWorkerSmartProxy;

import java.rmi.RemoteException;

public class DummyTLCWorker extends TLCWorkerSmartProxy implements TLCWorkerRMI {

    private final long duration;

    public DummyTLCWorker(final long duration) {
        super(null);
        this.duration = duration;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.TLCWorkerSmartProxy#getNextStates(tlc2.tool.TLCState[])
     */
    @Override
    public NextStateResult getNextStates(final TLCState[] states) throws RemoteException {
        return new NextStateResult(null, null, duration, -1L);
    }

    @Override
    public void close() {

    }
}
