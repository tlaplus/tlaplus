package tlc2.tool.queue;

import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.Worker;

import java.io.IOException;

public interface IStateQueue extends AutoCloseable {

    /* Enqueues the state. It is not thread-safe. */
    void enqueue(final TLCState state);

    /**
     * Returns the first element in the queue. It returns null if the queue is
     * empty. It is not thread-safe.
     */
    TLCState dequeue();

    /* Enqueues a state. Wake up any waiting thread. */
    void sEnqueue(final TLCState state);

    /* Enqueues a list of states. Wake up any waiting thread. */
    void sEnqueue(final TLCState[] states);

    void sEnqueue(final StateVec stateVec);

    /* Return the first element in the queue. Wait if empty. */
    TLCState sDequeue();

    /**
     * Returns the first element in the queue. Wait if empty. Does not remove the
     * element. Can be null and blocks other consumers (sEnqueue and sDequeue).
     */
    TLCState sPeek();

    /**
     * Return (up to) the first count elements in the queue. Wait if empty.
     *
     * @param cnt Amount of states requested
     * @return null iff no states are available && all work is done @see
     * {@link #isAvail()}, states otherwise
     * @throws RuntimeException if cnt <= 0
     */
    TLCState[] sDequeue(int cnt);

    /**
     * Signals all waiting {@link Worker} that all work is done. We can exit now.
     */
    void close() throws Exception;

    /**
     * Suspends all access to the {@link StateQueue} for {@link Worker},
     * potentially waiting for current accessing {@link Worker} to finish first.
     *
     * @return False iff {@link #finish} is true, true otherwise
     */
    boolean suspendAll();

    /**
     * Resumes waiting {@link Worker} after a checkpoint
     */
    void resumeAll();

    /**
     * This is a no-op in regular. The only case is, when a worker is stuck in
     * {@link #isAvail()}, {@link #isEmpty}, {@link #stop} is false and
     * {@link #numWaiting} > 0. Bottom-line, it is assumed to be side-effect
     * free when workers behave correctly except for the single case when a
     * remote worker dies unexpectedly.
     *
     * @see Bug #175 in general/bugzilla/index.html
     */
    void resumeAllStuck();

    /* This method returns the size of the state queue. */
    long size();

    /* Checkpoint. */
    void beginChkpt() throws IOException;

    void commitChkpt() throws IOException;

    void recover() throws IOException;

    boolean isEmpty();

    /**
     * TESTING ONLY!
     * Delete disk files if any.
     */
    void delete() throws Exception;
}