package tlc2.tool.queue;

import java.io.IOException;

import tlc2.tool.TLCState;
import tlc2.tool.Worker;

public interface IStateQueue {

	/* Enqueues the state. It is not thread-safe. */
	public abstract void enqueue(final TLCState state);

	/**
	 * Returns the first element in the queue. It returns null if the queue is
	 * empty. It is not thread-safe.
	 */
	public abstract TLCState dequeue();

	/* Enqueues a state. Wake up any waiting thread. */
	public abstract void sEnqueue(final TLCState state);

	/* Enqueues a list of states. Wake up any waiting thread. */
	public abstract void sEnqueue(final TLCState states[]);

	/* Return the first element in the queue. Wait if empty. */
	public abstract TLCState sDequeue();

	/**
	 * Return (up to) the first count elements in the queue. Wait if empty.
	 * 
	 * @param cnt
	 *            Amount of states requested
	 * @return null iff no states are available && all work is done @see
	 *         {@link #isAvail()}, states otherwise
	 * @throws RuntimeException
	 *             if cnt <= 0
	 */
	public abstract TLCState[] sDequeue(int cnt);

	/**
	 * Signals all waiting {@link Worker} that all work is done. We can exit now.
	 */
	public abstract void finishAll();

	/**
	 * Suspends all access to the {@link StateQueue} for {@link Worker},
	 * potentially waiting for current accessing {@link Worker} to finish first.
	 * 
	 * @return False iff {@link #finish} is true, true otherwise
	 */
	public abstract boolean suspendAll();

	/**
	 * Resumes waiting {@link Worker} after a checkpoint
	 */
	public abstract void resumeAll();

	/**
	 * This is a no-op in regular. The only case is, when a worker is stuck in
	 * {@link #isAvail()}, {@link #isEmpty}, {@link #stop} is false and
	 * {@link #numWaiting} > 0. Bottom-line, it is assumed to be side-effect
	 * free when workers behave correctly except for the single case when a
	 * remote worker dies unexpectedly.
	 * 
	 * @see http://bugzilla.tlaplus.net/show_bug.cgi?id=175
	 */
	public abstract void resumeAllStuck();

	/* This method returns the size of the state queue. */
	public abstract long size();

	/* Checkpoint. */
	public abstract void beginChkpt() throws IOException;

	public abstract void commitChkpt() throws IOException;

	public abstract void recover() throws IOException;

	public abstract boolean isEmpty();
}