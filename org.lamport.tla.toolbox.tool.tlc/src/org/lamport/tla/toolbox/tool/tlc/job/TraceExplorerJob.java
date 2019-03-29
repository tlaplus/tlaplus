package org.lamport.tla.toolbox.tool.tlc.job;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.swt.widgets.Display;

import tlc2.tool.fp.FPSetFactory;

/**
 * Extends {@link TLCProcessJob}.
 * 
 * Currently, the only differences between this class and
 * {@link TLCProcessJob} are the way in which
 * the results of the trace explorer are presented. The results
 * of trace exploration are always displayed upon completion of
 * TLC. In a run of TLC for model checking, the results may not be
 * displayed if the user chooses to run the job in the background.
 * 
 * This job also has a shorter timeout than {@link TLCProcessJob} when
 * checking if TLC is still running. This seems to make the trace explorer
 * run faster.
 * 
 * @author Daniel Ricketts
 *
 */
public class TraceExplorerJob extends TLCProcessJob
{

    public TraceExplorerJob(String specName, String modelName, ILaunch launch, int workers)
    {
        super(specName, modelName, launch, workers);
        timeout = 100;
    }

    /**
     * Always asynchronously runs the action returned by
     * {@link AbstractJob#getJobCompletedAction()}.
     */
    public void doFinish()
    {
        Display.getDefault().asyncExec(new Runnable() {
            public void run()
            {
                getJobCompletedAction().run();
            }
        });
    }

	// Veto several TLC command line arguments only relevant for regular model
	// checking but not for trace exploration. This demonstrates why
	// TraceExplorerJob shouldn't be a subclass of TLCJob.
    
	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.job.TLCJob#recover()
	 */
	@Override
	protected boolean recover() throws CoreException {
		// There is nothing that trace exploration could recover from.
		return false;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.job.TLCJob#isDepthFirst()
	 */
	@Override
	protected boolean isDepthFirst() throws CoreException {
		// Always want BFS in trace exploration.
		return false;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.job.TLCJob#runAsModelCheck()
	 */
	@Override
	protected boolean runAsModelCheck() throws CoreException {
		// We don't want trace exploration to run in simulation mode.
		return true;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.job.TLCJob#checkPoint()
	 */
	@Override
	protected boolean checkPoint() {
		// Why would the trace explorer create a checkpoint!?!
		return false;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.job.TLCJob#checkDeadlock()
	 */
	@Override
	protected boolean checkDeadlock() throws CoreException {
		// We override this method in order to always make sure that deadlock is always
		// checked. This method simply removes "-deadlock" from the array of arguments,
		// if it is present in the super class implementation of this method. The trace
		// requests deadlock checking - which is turned on when "-deadlock" is NOT set - 
		// is to always print a counterexample. This counterexample contains the 
		// evaluated expressions defined in Error-Trace exploration.
		return true;
	}

	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.job.TLCJob#visualizeStateGraph()
	 */
	@Override
	protected boolean visualizeStateGraph() throws CoreException {
		// Never use an IStateWriter to write out the states created by trace
		// exploration. A trace is just a txt file with a sequence of states.
		return false;
	}
	
    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.job.TLCJob#collectCoverage()
     */
	@Override
    protected boolean collectCoverage() throws CoreException {
		// No need for coverage statistics when running error trace exploration.
    	return false;
    }
	
	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.job.TLCJob#deferLiveness()
	 */
	@Override
    protected boolean deferLiveness() throws CoreException {
		// As a performance improvement, always defer liveness until the end of model
		// checking in trace exploration.
        return true;
    }
	
	/* (non-Javadoc)
	 * @see org.lamport.tla.toolbox.tool.tlc.job.TLCProcessJob#getOptimalFPsetImpl()
	 */
	@Override
	protected String getOptimalFPsetImpl() throws CoreException {
		// A trace is a single behavior of usually about a dozen states and sometimes a
		// few thousand. This range is easily handled by the default FPSet
		// implementation which is faster to initialize compared to the optimized
		// OffHeapDiskFPSet. This should make the trace explorer a lot snappier.
		return FPSetFactory.getImplementationDefault();
	}
}
