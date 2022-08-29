package tlc2.tool.liveness;

public class LiveWorkerSynchronization {

    final Object workerLock = new Object();
    int errFoundByThread = -1;

    public LiveWorkerSynchronization() {
    }

    /**
     * Returns true iff an error has already been found.
     */
    public boolean hasErrFound() {
        synchronized (workerLock) {
            return (errFoundByThread != -1);
        }
    }

    // True iff this LiveWorker found a liveness violation.zs
    public boolean hasErrFound(final int id) {
        synchronized (workerLock) {
            return (errFoundByThread == id);
        }
    }

    /**
     * Returns true iff either an error has not been found or the error is found
     * by this thread.
     * <p>
     * This is used so that only one of the threads which have found an error
     * prints it.
     */
    public boolean setErrFound(final int id) {
        synchronized (workerLock) {
            // (* GetId()) {
            if (errFoundByThread == -1) {
                errFoundByThread = id; // GetId();
                return true;
            } else return errFoundByThread == id;
        }
    }
}
