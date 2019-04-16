package tlc2.tool;

import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.util.ObjLongTable;
import tlc2.value.IValue;

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
	
    /** 
     * extracted from Worker and DFID worker
     * used in the {@link AbstractChecker#reportCoverage(IWorker[])} 
     */
    public ObjLongTable<SemanticNode> getCounts();

    // see Thread
    
	public void start();

	public void join() throws InterruptedException;

	// see IdThread
	
	public IValue getLocalValue(int idx);

	public void setLocalValue(int idx, IValue val);
}
