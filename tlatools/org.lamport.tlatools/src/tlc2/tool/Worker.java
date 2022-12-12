// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 14:01:40 PST by lamport  
//      modified on Wed Dec  5 15:35:42 PST 2001 by yuanyu   

package tlc2.tool;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.Arrays;
import java.util.LinkedList;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.fp.FPSet;
import tlc2.tool.impl.CallStackTool;
import tlc2.tool.impl.Tool;
import tlc2.tool.impl.Tool.Mode;
import tlc2.tool.queue.IStateQueue;
import tlc2.util.BufferedRandomAccessFile;
import tlc2.util.IStateWriter;
import tlc2.util.IdThread;
import tlc2.util.SetOfStates;
import tlc2.util.statistics.FixedSizedBucketStatistics;
import tlc2.util.statistics.IBucketStatistics;
import tlc2.value.impl.CounterExample;
import util.Assert;
import util.Assert.TLCRuntimeException;
import util.FileUtil;
import util.WrongInvocationException;

public final class Worker extends IdThread implements IWorker, INextStateFunctor {

	protected static final boolean coverage = TLCGlobals.isCoverageEnabled();
	private static final int INITIAL_CAPACITY = 16;
	
	/**
	 * Multi-threading helps only when running on multiprocessors. TLC can
	 * pretty much eat up all the cycles of a processor running single threaded.
	 * We expect to get linear speedup with respect to the number of processors.
	 */
	private final ModelChecker tlc;
	private final Tool tool;
	private final Mode mode;
	private final IStateQueue squeue;
	private final FPSet theFPSet;
	private final IStateWriter allStateWriter;
	private final IBucketStatistics outDegree;
	private final String filename;
	private final BufferedRandomAccessFile raf;
	private final boolean checkDeadlock;

	private long lastPtr;
	private long statesGenerated;
	private int unseenSuccessorStates = 0;
	private volatile int maxLevel = 0;

	// SZ Feb 20, 2009: changed due to super type introduction
	public Worker(int id, AbstractChecker tlc, String metadir, String specFile) throws IOException {
		super(id);
		// SZ 12.04.2009: added thread name
		this.setName("TLC Worker " + id);
		this.tlc = (ModelChecker) tlc;
		this.checkLiveness = this.tlc.checkLiveness;
		this.checkDeadlock = this.tlc.checkDeadlock;
		this.tool = (Tool) this.tlc.tool;
		this.mode = this.tool.getMode();
		this.squeue = this.tlc.theStateQueue;
		this.theFPSet = this.tlc.theFPSet;
		this.allStateWriter = this.tlc.allStateWriter;
		this.outDegree = new FixedSizedBucketStatistics(this.getName(), 32); // maximum outdegree of 32 appears sufficient for now.
		this.setName("TLCWorkerThread-" + String.format("%03d", id));

		this.filename = metadir + FileUtil.separator + specFile + "-" + myGetId();
		this.raf = new BufferedRandomAccessFile(filename + TLCTrace.EXT, "rw");
	}

	/**
   * This method gets a state from the queue, generates all the
   * possible next states of the state, checks the invariants, and
   * updates the state set and state queue.
	 */
	public void run() {
		TLCState curState = null;
		try {
			while (true) {
				curState = this.squeue.sDequeue();
				if (curState == null) {
					synchronized (this.tlc) {
						if(!this.tlc.setDone()) {
							final int ec = tool.checkPostCondition();
							if (ec != EC.NO_ERROR) {
								tlc.setError(true, ec);
							}
						}
						this.tlc.notify();
					}
					//TODO: finishAll not inside the synchronized block above, while
					//inside in a similar construct below (Throwable catch)?!
					this.squeue.finishAll();
					return;
				}
				setCurrentState(curState);
				
				if (this.checkLiveness || mode == Mode.MC_DEBUG) {
					// Allocate iff liveness is checked.
					setOfStates = createSetOfStates();
				}
				
				final long preNext = this.statesGenerated;
				try {
					this.tool.getNextStates(this, curState);
				} catch (final WrappingRuntimeException e) {
					// The next-state relation couldn't be evaluated. If doNextFailed itself throws
					// a Throwable, the catch block below will handle it.
					this.tlc.doNextFailed(curState, e.unwrapState(), e.unwrapExp());
				} catch (final Throwable notExpectedToHappen) {
					this.tlc.doNextFailed(curState, null, notExpectedToHappen);
				}
				
				if (this.checkDeadlock && preNext == this.statesGenerated) {
					// A deadlock is defined as a state without (seen or unseen) successor
					// states. In other words, evaluating the next-state relation for a state
					// yields no states.
	                this.doNextSetErr(curState, null, false, EC.TLC_DEADLOCK_REACHED, null);
				}
				
	            // Finally, add curState into the behavior graph for liveness checking:
	            if (this.checkLiveness)
	            {
	            	try {
	            		doNextCheckLiveness(curState, setOfStates);
					} catch (final Throwable e) {
						this.tlc.doNextFailed(curState, null, e);
	            	}
	            }
				
				this.outDegree.addSample(unseenSuccessorStates);
				unseenSuccessorStates = 0;
			}
		} catch (Throwable e) {
			// Something bad happened. Quit ...
			// Assert.printStack(e);
			resetCurrentState();
			synchronized (this.tlc) {
				if (this.tlc.setErrState(curState, null, true, EC.GENERAL)) {
					MP.printError(EC.GENERAL, e); // LL changed call 7 April 2012
				}
				this.squeue.finishAll();
				this.tlc.notify();
			}
			return;
		}
	}
	
	/* Liveness */
	
	private int multiplier = 1;

	private SetOfStates setOfStates;

	private final boolean checkLiveness;

	private final void doNextCheckLiveness(TLCState curState, SetOfStates liveNextStates) throws IOException {
		final long curStateFP = curState.fingerPrint();

		// Add the stuttering step:
		liveNextStates.put(curStateFP, curState);
		this.tlc.allStateWriter.writeState(curState, curState, true, IStateWriter.Visualization.STUTTERING);

		// Contrary to exceptions that are thrown during the evaluation of the init
		// predicate and the next-state relation, the code below causes the call stack
		// to be printed first and only then the trace.  Ordinary safety checking first
		// prints the trace followed by the call stack.  The Toolbox is oblivious because
		// it parses the output.  Command-line users, however, might miss the call stack.
		// Perhaps, it would be best to attach CallStack to the exception and let the
		// global exception handling take care of it. Unfortunately, TLC's exception
		// handling is a mess: a) TLCRuntimException and EvalException overlap b)
		// CallStackTool cannot always be enabled at the site where exceptions
		// originate, and c) there is no global exception handling.
		try {
			this.tlc.liveCheck.addNextState(tlc.tool.getLiveness(), curState, curStateFP, liveNextStates);
		} catch (EvalException | TLCRuntimeException origExp) {
			synchronized (this.tlc) {
				if (this.tlc.printedLivenessErrorStack) {
					// Another worker beat us to printing an error trace.
					return; 
				}
				this.tlc.printedLivenessErrorStack= true;
				
				// liveCheck#addNextState throws an EvalException if, e.g., a Java module overrides throw one:
				// For example: `Cardinality(S) ~> ...` with `S` a naturals, ...

				// Reset the iterator before using it again after the call to addNextState above.
				liveNextStates.resetNext();

				// TODO: Try to pass DebugTool instead of tool.getLiveness to enable the TLC
				// debugger for liveness checking.
				final CallStackTool cTool = new CallStackTool(tlc.tool.getLiveness());
				try {
					this.tlc.liveCheck.addNextState(cTool, curState, curStateFP, liveNextStates);
					// Regular evaluation with tlc.tool.getLiveness failed but CallStackTool
					// succeeded. This should never happen!
					Assert.fail(EC.GENERAL, origExp);
				} catch (EvalException | TLCRuntimeException rerunExp) {
					// liveCheck#addNextState is not side-effect free. For example, the behavior
					// (liveness) graph might have been changed and new GraphNodes been added. If
					// that's the case, calling addNextStates with the same parameters again causes
					// different exceptions. Those exception are bogus and should not be shown to the
					// user.
					// I don't expect equals to do the right thing(tm) for EvalException and/or
					// TLCRuntimeException. We effectively expect the same exception gets
					// throw by calling addNextState again.
					//assert origExp.getClass().isAssignableFrom(rerunExp.getClass());
					//assert origException.equals(rerunException);
					
					if (cTool.hasCallStack()) {
						// Tell ModelChecker.java not to re-run model-checking to re-create the error
						// stack because it was already re-created here.
						this.tlc.keepCallStack = false;
						// Do not handle the exception here but send it up the stack.
						// ModelChecker#doNextFailed puts this exception into context and prints the
						// current (prefix of) the behavior.
						MP.printError(EC.TLC_NESTED_EXPRESSION, cTool.toString());
					}
				}
				throw origExp;
			}
		}

		if (liveNextStates.capacity() > (multiplier * INITIAL_CAPACITY)) {
			// Increase initial size for as long as the set has to grow
			multiplier++;
		}
	}
	
	private final SetOfStates createSetOfStates() {
		return new SetOfStates(multiplier * INITIAL_CAPACITY);
	}
	
	@Override
	public SetOfStates getStates() {
		return setOfStates;
	}
	
	/* Statistics */

	final void incrementStatesGenerated(long l) {
		this.statesGenerated += l;		
	}
	
	final long getStatesGenerated() {
		return this.statesGenerated;
	}

	public final IBucketStatistics getOutDegree() {
		return this.outDegree;
	}
	
	public final int getMaxLevel() {
		return maxLevel;
	}

	final void setLevel(int level) {
		maxLevel = level;
	}

	/* Maintain trace file (to reconstruct error-trace) */
	
	/*
	 * Synchronize reads and writes to read a consistent union of all trace file
	 * fragments when one worker W wants to create the counter-example. Otherwise, we
	 * might not be able to correctly trace the path from state to an initial state.
	 * The W thread holds ModelChecker.this. The other workers might either: a) Wait
	 * on IStateQueue#sDequeue (waiting for a new state to be read from disk or
	 * added to the queue) b) Wait on ModelChecker.this (because they also found
	 * another counter-example but are blocked until we are done printing it) c)
	 * Wait on ModelChecker.this in Worker#run because the state queue is empty and
	 * they which to terminate. d) Run state space exploration The on-disk file of
	 * each worker's trace fragment is potentially inconsistent because the worker's
	 * cache in BufferedRandomAccessFile hasn't been flushed out.
	 */
	
	public final synchronized void writeState(final TLCState initialState, final long fp) throws IOException {
		// Write initial state to trace file.
		this.lastPtr = this.raf.getFilePointer();
		this.raf.writeLongNat(1L);
		this.raf.writeShortNat(myGetId());
		this.raf.writeLong(fp);
		
		// Add predecessor pointer to success state.
		initialState.workerId = (short) myGetId();
		initialState.uid = this.lastPtr;
	}

	public final synchronized void writeState(final TLCState curState, final long sucStateFp, final TLCState sucState) throws IOException {
		// Keep track of maximum diameter.
		maxLevel = Math.max(curState.getLevel() + 1, maxLevel);
		
		// Write to trace file.
		this.lastPtr = this.raf.getFilePointer();
		this.raf.writeLongNat(curState.uid);
		this.raf.writeShortNat(curState.workerId);
		this.raf.writeLong(sucStateFp);
		
		// Add predecessor pointer to success state.
		sucState.workerId = (short) myGetId();
		sucState.uid = this.lastPtr;
		
		sucState.setPredecessor(curState);
		
    	unseenSuccessorStates++;
		
//		System.err.println(String.format("<<%s, %s>>: pred=<<%s, %s>>, %s -> %s", myGetId(), this.lastPtr, 
//				curState.uid, curState.workerId,
//				curState.fingerPrint(), sucStateFp));
	}

	// Read from previously written (see writeState) trace file.
	public final synchronized ConcurrentTLCTrace.Record readStateRecord(final long ptr) throws IOException {
		// Remember current tip of the file before we rewind.
		this.raf.mark();
		
		// rewind to position we want to read from.
		this.raf.seek(ptr);
		
		final long prev = this.raf.readLongNat();
		assert 0 <= ptr;
		
		final int worker = this.raf.readShortNat();
		assert 0 <= worker && worker < tlc.workers.length;
			
		final long fp = this.raf.readLong();
		assert tlc.theFPSet.contains(fp);
		
		// forward/go back back to tip of file.
		// This is only necessary iff TLC runs with '-continue'. In other words, state
		// space exploration continues after an error trace has been written.
		this.raf.seek(this.raf.getMark());
		
		return new ConcurrentTLCTrace.Record(prev, worker, fp);
	}
	
	/* Checkpointing */

	public final synchronized void beginChkpt() throws IOException {
		this.raf.flush();
		final DataOutputStream dos = FileUtil.newDFOS(filename + ".tmp");
		dos.writeLong(this.raf.getFilePointer());
		dos.writeLong(this.lastPtr);
		dos.close();
	}

	public final synchronized void commitChkpt() throws IOException {
		final File oldChkpt = new File(filename + ".chkpt");
		final File newChkpt = new File(filename + ".tmp");
		if ((oldChkpt.exists() && !oldChkpt.delete()) || !newChkpt.renameTo(oldChkpt)) {
			throw new IOException("Trace.commitChkpt: cannot delete " + oldChkpt);
		}
	}

	public final void recover() throws IOException {
		final DataInputStream dis = FileUtil.newDFIS(filename + ".chkpt");
		final long filePos = dis.readLong();
		this.lastPtr = dis.readLong();
		dis.close();
		this.raf.seek(filePos);
	}
	
	/* Enumerator */
	
	public final Enumerator elements() throws IOException {
		return new Enumerator();
	}

	public class Enumerator {

		private final long len;
		private final BufferedRandomAccessFile enumRaf;

		Enumerator() throws IOException {
			this.len = raf.getFilePointer();
			this.enumRaf = new BufferedRandomAccessFile(filename + TLCTrace.EXT, "r");
		}

		public boolean hasMoreFP() {
			final long fpos = this.enumRaf.getFilePointer();
			if (fpos < this.len) {
				return true;
			}
			return false;
		}

		public long nextFP() throws IOException {
			this.enumRaf.readLongNat(); /* drop */
			this.enumRaf.readShortNat(); /* drop */
			return this.enumRaf.readLong();
		}

		public void close() throws IOException {
			this.enumRaf.close();
		}
	}
	
	//**************************************************************//

	@Override
	public final Object addElement(final TLCState state) {
		throw new WrongInvocationException("tlc2.tool.Worker.addElement(TLCState) should not be called");
	}

	@Override
	public final Object addElement(final TLCState curState, final Action action, final TLCState succState) {
	    if (coverage) { action.cm.incInvocations(); }
		this.statesGenerated++;
		
		try {
			if (!this.tool.isGoodState(succState)) {
				this.doNextSetErr(curState, succState, action);
				// It seems odd to subsume this under IVE, but we consider
				// it an invariant that the values of all variables have to
				// be defined.
				throw new InvariantViolatedException();
			}
			
			// Check if state is excluded by a state or action constraint.
			// Set the predecessor to make TLC!TLCGet("level") work in
			// state constraints, i.e. isInModel.
			final boolean inModel = (this.tool.isInModel(succState.setPredecessor(curState).setAction(action))
					&& this.tool.isInActions(curState, succState));
			
			// Check if state is new or has been seen earlier.
			boolean unseen = true;
			if (inModel) {
				unseen = !isSeenState(curState, succState, action);
			}
			
			// Check if succState violates any invariant:
			if (unseen) {
				if (this.doNextCheckInvariants(curState, succState)) {
					throw new InvariantViolatedException();
				}
			}
			
			// Check if the state violates any implied action. We need to do it
			// even if succState is not new.
			if (this.doNextCheckImplied(curState, succState)) {
				throw new InvariantViolatedException();
			}
			
			if (inModel && unseen) {
				// The state is inModel, unseen and neither invariants
				// nor implied actions are violated. It is thus eligible
				// for further processing by other workers.
				this.squeue.sEnqueue(succState);
			}
			return this;
		} catch (Exception e) {
			// We can't throw Exception here because it would violate the contract of
			// tlc2.tool.INextStateFunctor.addElement(TLCState, Action, TLCState). Thus,
			// wrap the exception regardless of whether it is a (unchecked) runtime
			// exception or not. We expect the outer code in run(..) above to unwrap this
			// exception.  As a bonus, we can attach succState and send it up the stack.
			throw new WrappingRuntimeException(e, succState);
		}
	}
	
	@SuppressWarnings("serial")
	private static class WrappingRuntimeException extends RuntimeException {

		private final Exception e;
		private final TLCState state;

		public WrappingRuntimeException(final Exception e, final TLCState state) {
			this.e = e;
			this.state = state;
		}
		
		public TLCState unwrapState() {
			return state;
		}

		public Exception unwrapExp() {
			return e;
		}
	}

	private final boolean isSeenState(final TLCState curState, final TLCState succState, final Action action)
			throws IOException {
		final long fp = succState.fingerPrint();
		final boolean seen = this.theFPSet.put(fp);
		// Write out succState when needed:
		this.allStateWriter.writeState(curState, succState, !seen, action);
		if (!seen) {
			// Write succState to trace only if it satisfies the
			// model constraints. Do not enqueue it yet, but wait
			// for implied actions and invariants to be checked.
			// Those checks - if violated - will cause model checking
			// to terminate. Thus we cannot let concurrent workers start
			// exploring this new state. Conversely, the state has to
			// be in the trace in case either invariant or implied action
			// checks want to print the trace.
			this.writeState(curState, fp, succState);
			if (coverage) {	action.cm.incSecondary(); }
		}
		// For liveness checking:
		if (this.checkLiveness || mode == Mode.MC_DEBUG)
		{
			this.setOfStates.put(fp, succState);
		}
		return seen;
	}

	private final boolean doNextCheckInvariants(final TLCState curState, final TLCState succState) throws IOException, WorkerException, Exception {
        int k = 0;
		try
        {
			for (k = 0; k < this.tool.getInvariants().length; k++)
            {
                if (!tool.isValid(this.tool.getInvariants()[k], succState))
                {
                    // We get here because of invariant violation:
                	if (TLCGlobals.continuation) {
                        synchronized (this.tlc)
                        {
							MP.printError(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR,
									this.tool.getInvNames()[k]);
							this.tlc.trace.printTrace(curState, succState);
							return false;
                        }
                	} else {
						return this.doNextSetErr(curState, succState, false,
								EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, this.tool.getInvNames()[k]);
                	}
				}
			}
        } catch (Exception e)
        {
			this.tlc.doNextEvalFailed(curState, succState, EC.TLC_INVARIANT_EVALUATION_FAILED,
					this.tool.getInvNames()[k], e);
		}
		return false;
	}

	private final boolean doNextCheckImplied(final TLCState curState, final TLCState succState) throws IOException, WorkerException, Exception {
		int k = 0;
        try
        {
			for (k = 0; k < this.tool.getImpliedActions().length; k++)
            {
                if (!tool.isValid(this.tool.getImpliedActions()[k], curState, succState))
                {
                    // We get here because of implied-action violation:
                    if (TLCGlobals.continuation)
                    {
                        synchronized (this.tlc)
                        {
                            MP.printError(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR, this.tool
                                    .getImpliedActNames()[k]);
                            this.tlc.trace.printTrace(curState, succState);
							return false;
                       }
                    } else {
						return this.doNextSetErr(curState, succState, false,
								EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR,
								this.tool.getImpliedActNames()[k]);
                	}
				}
			}
        } catch (Exception e)
        {
        	this.tlc.doNextEvalFailed(curState, succState, EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED,
					this.tool.getImpliedActNames()[k], e);
		}
        return false;
	}
	
	private boolean doNextSetErr(TLCState curState, TLCState succState, boolean keep, int ec, String param) throws IOException, WorkerException {
		synchronized (this.tlc) {
			final boolean doNextSetErr = this.tlc.doNextSetErr(curState, succState, keep, ec, param);

			// Invoke PostCondition
			doPostCondition(curState, succState);
			
			return doNextSetErr;
		}
	}
	
	private boolean doNextSetErr(TLCState curState, TLCState succState, Action action) throws IOException, WorkerException {
		synchronized (this.tlc) {
			final boolean doNextSetErr = this.tlc.doNextSetErr(curState, succState, action);

			// Invoke PostCondition
			doPostCondition(curState, succState);

			return doNextSetErr;
		}
	}
	
	private final void doPostCondition(TLCState curState, TLCState succState) throws IOException {
		final LinkedList<TLCStateInfo> trace = new LinkedList<>();
		if (curState.isInitial() && succState == null) {
			// Prevents calling tool.getState(initial, initial) in the next else-if branch.
			trace.add(tool.getState(curState.fingerPrint()));
		} else if (succState == null) {
			trace.addAll(Arrays.asList(tlc.getTraceInfo(curState)));
			trace.add(tool.getState(curState, trace.getLast().state));
		} else {
			trace.addAll(Arrays.asList(tlc.getTraceInfo(succState)));
			trace.add(tool.getState(succState, curState));
		}
		tool.checkPostConditionWithCounterExample(new CounterExample(trace));
	}
}
