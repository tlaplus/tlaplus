package tlc2.tool;

import tlc2.TLCGlobals;
import tlc2.value.Value;

/**
 * A common interface for workers
 * @author Simon Zambrovski
 */
public interface IWorker
{
	/**
	 * @return A worker's id in the range 0 to {@link TLCGlobals#getNumWorkers()} - 1
	 */
	public int myGetId();
	
    // see Thread
    
	public void start();

	public void join() throws InterruptedException;

	// see IdThread
	
	public Value getLocalValue(int idx);

	public void setLocalValue(int idx, Value val);
}
