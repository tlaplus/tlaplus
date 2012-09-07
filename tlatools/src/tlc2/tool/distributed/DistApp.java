// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:25:56 PST by lamport
//      modified on Thu May 31 13:22:22 PDT 2001 by yuanyu

package tlc2.tool.distributed;

import java.rmi.RemoteException;

import tlc2.tool.TLCState;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.TraceApp;
import tlc2.tool.WorkerException;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class DistApp implements TraceApp {

	// TLCServer
	public abstract Boolean getCheckDeadlock();

	// TLCServer
	public abstract Boolean getPreprocess();

	// TLCServer
	public abstract String getFileName();

	// TLCServer
	public abstract String getMetadir();

	// TLCServer
	public abstract boolean canRecover();

	// Returns a list of initial states.
	// TLCServer
	public abstract TLCState[] getInitStates() throws WorkerException;

	// Returns a list of successor states of the state s. /
	// TLCServer
	public abstract TLCState[] getNextStates(TLCState s) throws WorkerException, RemoteException;

	// Checks if the state is a valid state.
	// TLCServer, TLCWorker
	public abstract void checkState(TLCState s1, TLCState s2)
			throws WorkerException;

	// Checks if the state satisfies the state constraints.
	// TLCServer, TLCWorker
	public abstract boolean isInModel(TLCState s);

	// Checks if a pair of states satisfy the action constraints.
	// TLCWorker
	public abstract boolean isInActions(TLCState s1, TLCState s2);

	// Reconstruct the initial state whose fingerprint is fp.
	// TLCTrace
	/* (non-Javadoc)
	 * @see tlc2.tool.TraceApp#getState(long)
	 */
	public abstract TLCStateInfo getState(long fp);

	// Reconstruct the next state of state s whose fingerprint is fp.
	// TLCTrace
	/* (non-Javadoc)
	 * @see tlc2.tool.TraceApp#getState(long, tlc2.tool.TLCState)
	 */
	public abstract TLCStateInfo getState(long fp, TLCState s);

	// Reconstruct the info for the transition from s to s1. /
	// TLCTrace
	/* (non-Javadoc)
	 * @see tlc2.tool.TraceApp#getState(tlc2.tool.TLCState, tlc2.tool.TLCState)
	 */
	public abstract TLCStateInfo getState(TLCState s1, TLCState s);

	// Enables call stack tracing.
	// TLCServer
	public abstract void setCallStack();

	// Prints call stack.
	// TLCServer
	public abstract String printCallStack();

	/**
	 * @return The specification root directory
	 */
	// TLCServer
	public abstract String getSpecDir();

	/**
	 * @return The (qualified) configuration file name
	 */
	// TLCServer
	public abstract String getConfigName();
}
