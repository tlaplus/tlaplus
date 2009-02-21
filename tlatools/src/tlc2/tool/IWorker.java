package tlc2.tool;

import tlc2.util.ObjLongTable;

/**
 * A common interface for workers
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IWorker
{
    /** 
     * extracted from Worker and DFID worker
     * used in the {@link AbstractChecker#reportCoverage(IWorker[])} 
     */
    public ObjLongTable getCounts();
}
