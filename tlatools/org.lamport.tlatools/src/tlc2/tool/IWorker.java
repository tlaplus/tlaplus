package tlc2.tool;

import tlc2.TLCGlobals;
import tlc2.value.IValue;

/**
 * A common interface for workers
 *
 * @author Simon Zambrovski
 */
public interface IWorker {
    /**
     * @return A worker's id in the range 0 to {@link TLCGlobals#getNumWorkers()} - 1
     */
    int myGetId();

    // see Thread

    void start();

    void join() throws InterruptedException;

    // see IdThread

    IValue getLocalValue(int idx);

    void setLocalValue(int idx, IValue val);
}
