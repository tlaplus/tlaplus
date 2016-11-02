package tlc2.tool;

import tlc2.util.ObjLongTable;
import tlc2.value.Value;

/**
 * A common interface for workers
 * @author Simon Zambrovski
 */
public interface IWorker
{
    /** 
     * extracted from Worker and DFID worker
     * used in the {@link AbstractChecker#reportCoverage(IWorker[])} 
     */
    public ObjLongTable getCounts();

    // see Thread
    
	public void start();

	public void join() throws InterruptedException;

	// see IdThread
	
	public Value getLocalValue(int idx);

	public void setLocalValue(int idx, Value val);
}
