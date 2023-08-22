/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   William Schultz - initial API and implementation
 ******************************************************************************/
package tlc2.tool;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.LongAdder;
import java.util.function.Supplier;
import java.util.stream.Collectors;

import tla2sany.semantic.OpDeclNode;
import tlc2.TLCGlobals;
import tlc2.module.TLCGetSet;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.impl.Tool;
import tlc2.tool.liveness.ILiveCheck;
import tlc2.tool.liveness.LiveCounterExampleException;
import tlc2.util.IdThread;
import tlc2.util.RandomGenerator;
import tlc2.util.SetOfStates;
import tlc2.value.impl.CounterExample;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.Value;
import util.FileUtil;
import util.UniqueString;

/**
 * A SimulationWorker repeatedly checks random traces of a spec.
 * 
 * It is constructed with an initial seed which it uses to initialize its
 * internal random number generator. A simulation worker continually generates
 * random traces, even if it encounters errors of any kind i.e.
 * invariant/liveness violations, evaluation errors, etc. A worker communicates
 * these errors by pushing its results onto a result queue, that is provided to
 * it at construction time.
 * 
 * Workers may terminate in two possible ways. They will terminate if they
 * receive an "interruption" signal, and they will terminate if they reach their
 * maximum trace count limit. Otherwise, they will continue to run forever,
 * generating new traces. It is the job of an external thread/client to
 * determine if the errors produced are cause for termination or can be ignored.
 * 
 * Upon termination due to any cause, a worker thread will always push a final
 * OK result onto its result queue. This acts as a way to signal external
 * clients that this thread has terminated.
 */
public class SimulationWorker extends IdThread implements INextStateFunctor {

	protected static final boolean coverage = TLCGlobals.isCoverageEnabled();

	// This worker's local source of randomness.
	private final RandomGenerator localRng;

	// The state currently being processed.
	private TLCState curState;

	// The set of initial states for the spec. 
	private StateVec initStates;
	
	// The queue that the worker places its results onto.
	private final BlockingQueue<SimulationWorkerResult> resultQueue;
	
	// Tracks the number of traces that have been generated so far.
	private long traceCnt = 0;
	private long globalTraceCnt = 0;
	
	// The maximum number of traces this worker should generate before terminating.
	private final long maxTraceNum;
	
	// The maximum length of any generated trace.
	private final int maxTraceDepth;
	
	// Should this worker check traces for deadlock.
	private final boolean checkDeadlock;
	
	// The base name of the file that this worker writes out generated traces to. If it is null,
	// no trace files are generated.
	private final String traceFile;

	private final ITool tool;
	private final ILiveCheck liveCheck;	

	final SimulationWorkerStatistics statistics;
	
	/**
	 * Encapsulates information about an error produced by a simulation worker.
	 */
	 public static class SimulationWorkerError extends InvariantViolatedException  {
		public SimulationWorkerError(int errorCode, String[] parameters, TLCState state, StateVec stateTrace) {
			this(errorCode, parameters, state, stateTrace, null);
		}
		
		public SimulationWorkerError(int errorCode, String[] parameters, TLCState state, StateVec stateTrace,
				Exception e) {
			this.errorCode = errorCode;
			this.parameters = parameters;
			this.state = state;
			this.stateTrace = stateTrace;
			this.exception = e;
		}
		
		// The error code to report.
		public int errorCode;

		// Any additional information to be included in a reported error string.
		public final String[] parameters;

		// The TLC state associated with the error.
		public final TLCState state;

		// The TLC trace associated with the error.
		public final StateVec stateTrace;

		// An exception associated with the error.
		public final Exception exception;

		@Override
		public String getMessage() {
			return MP.getMessage(errorCode, parameters);
		}

		public boolean hasTrace() {
			return stateTrace != null && !stateTrace.empty();
		}

		public List<TLCStateInfo> getTrace() {
			final ArrayList<TLCStateInfo> trace = new ArrayList<>();
			for (int j = 0; j < stateTrace.size(); j++) {
				final TLCState state = stateTrace.elementAt(j);
				trace.add(new TLCStateInfo(state, state.getAction()));
			}			
			return trace;
		}

		public CounterExample getCounterExample() {
			if (exception instanceof LiveCounterExampleException) {
				return ((LiveCounterExampleException) exception).counterExample;
			}
			return new CounterExample(getTrace());
		}
	}
	
	
	/**
	 * Encapsulates information about a result produced by a simulation worker.
	 * 
	 * A result can either be an error or OK (indicating no error). Each result is
	 * associated with a specific worker.
	 */
	public static class SimulationWorkerResult {
		
		/**
		 * Constructs an OK result.
		 */
		static SimulationWorkerResult OK(int workerId) {
			SimulationWorkerResult res = new SimulationWorkerResult();
			res.workerId = workerId;
			return res;
		}
			
		/**
		 * Constructs an error result.
		 */
		static SimulationWorkerResult Error(int workerId, SimulationWorkerError err) {
			SimulationWorkerResult res = new SimulationWorkerResult();
			res.error = Optional.of(err);
			res.workerId = workerId;
			return res;
		}

		/**
		 * Returns whether this result is an error.
		 */
		public boolean isError() {
			return error.isPresent();
		}
		
		/**
		 * Returns the error for this result. Only valid to call if an error is present.
		 */
		public SimulationWorkerError error() {
			return error.get();
		}
		
		public int workerId() {
			return workerId;
		}
		
		private int workerId; // The worker that generated this result.
		private Optional<SimulationWorkerError> error = Optional.empty();
	}
	
	class SimulationWorkerStatistics {

		private final String traceActions;
		
		// A counter that tracks the number of generated states/traces. This counter may be
		// shared among workers, so its count may be greater than the number of states/traces
		// generated by this worker alone. It is the duty of this worker, though, to
		// update it whenever it generates a new state or trace.
		private final LongAdder numOfGenStates;
		private final AtomicLong numOfGenTraces;
		
		private final AtomicLong welfordM2AndMean;
		
		// Adjacency Matrix with link weights.
		final long[][] actionStats;

		public SimulationWorkerStatistics(final String traceActions, final LongAdder numOfGenStates,
				final AtomicLong numOfGenTraces, final AtomicLong m2AndMean) {
			this.traceActions = traceActions;
			
			// Cheap (constant): Aggregated statistics about the number of generated states and traces.
			this.numOfGenStates = numOfGenStates;
			this.numOfGenTraces = numOfGenTraces;
			
			// Cheap (constant): Aggregated statistics about the average length, SD, ... about the traces.
			this.welfordM2AndMean = m2AndMean;

			// Moderate (quadratic in the number of actions): 
			if (traceActions != null) {
				final int len = tool.getSpecActions().size();
				this.actionStats = new long[len][len];
			} else {
				// Write all statistics into a single cell that we will ignore.
				this.actionStats = new long[1][1];
			}
		}

		public void collectPreSuccessor(final TLCState s, final Action a, final TLCState t) {
			numOfGenStates.increment();
		}

		public void collectPostSuccessor(final TLCState s, final Action a, final TLCState t) {
			// In case actionStats are off, we waste a few cycles to increment this counter
			// nobody is going to look at.
			if (traceActions != null) {
				this.actionStats[s.getAction().getId()][t.getAction().getId()]++;
			}
		}

		public long collectPreTrace() {
			return numOfGenTraces.incrementAndGet();
		}

		public void collectPostTrace(final TLCState s) {
			// Take the minimum of maxTraceDepth and getLevel here because - historically -
			// the for loop above would add the chosen next-state from loop N in loop N+1.
			// Thus, the final state that is generated before traceCnt = maxTraceDepth,
			// wasn't getting added to the stateVec (check git history) whose length was
			// passed to welfordM2AndMean.
			welfordM2AndMean.accumulateAndGet(Math.min(maxTraceDepth, s.getLevel()), (acc, tl) -> {
				// Welford's online algorithm (m2 and mean stuffed into high and low of the
				// atomiclong because welfordM2AndMean is updated concurrently by multiple workers).
				// https://en.wikipedia.org/wiki/Algorithms_for_calculating_variance#Welford's_online_algorithm
				int mean = (int) (acc & 0x00000000FFFFFFFFL);
				long m2 = acc >>> 32;
				final long delta = tl - mean;
				mean += delta / (numOfGenTraces.longValue() + 0); //+1 prevent div-by-zero
				m2 += delta * (tl - mean);
				return m2 << 32 | (mean & 0xFFFFFFFFL);
			});
		}
		
		//*************************** Reporting **************************//

		public Value getWorkerStatistics(TLCState s) {
			final UniqueString[] n = new UniqueString[2];
			final Value[] v = new Value[n.length];
			
			// Cheap (linear in the number of actions): Statistics about the occurrences of
			// actions in the *current* behavior.
			final Map<UniqueString, IntValue> behaviorStats = new HashMap<>();	
			while (s != null && !s.isInitial()) {
				behaviorStats.merge(s.getAction().getName(), IntValue.ValOne, IntValue::sum);
				s = s.getPredecessor();
			}
			n[0] = TLCGetSet.SPEC_ACTIONS;
			v[0] = new RecordValue(behaviorStats);
			
			n[1] = TLCGetSet.ID;
			v[1] = TLCGetSet.narrowToIntValue(globalTraceCnt);
			
			return new RecordValue(n, v, false);
		}
	}
	
	public SimulationWorker(int id, ITool tool, BlockingQueue<SimulationWorkerResult> resultQueue,
			long seed, int maxTraceDepth, long maxTraceNum, boolean checkDeadlock, String traceFile,
			ILiveCheck liveCheck) {
		this(id, tool, resultQueue, seed, maxTraceDepth, maxTraceNum, null, checkDeadlock, traceFile, liveCheck,
				new LongAdder(), new AtomicLong(), new AtomicLong());
	}

	public SimulationWorker(int id, ITool tool, BlockingQueue<SimulationWorkerResult> resultQueue,
			long seed, int maxTraceDepth, long maxTraceNum, String traceActions, boolean checkDeadlock, String traceFile,
			ILiveCheck liveCheck, LongAdder numOfGenStates, AtomicLong numOfGenTraces, AtomicLong m2AndMean) {
		super(id);
		this.localRng = new RandomGenerator(seed);
		this.tool = tool;
		this.maxTraceDepth = maxTraceDepth;
		this.maxTraceNum = maxTraceNum;
		this.resultQueue = resultQueue;
		this.checkDeadlock = checkDeadlock;
		this.traceFile = traceFile;
		this.liveCheck = liveCheck;
		this.statistics = new SimulationWorkerStatistics(traceActions, numOfGenStates, numOfGenTraces, m2AndMean);
	}
	
	/**
	 * The main worker loop. Continually generates random traces until the trace count limit
	 * is reached or until the worker is interrupted.
	 * 
	 * We use the standard Java notion of thread "interruption" as a mechanism for
	 * halting/cancelling the execution of a worker thread. There's nothing particularly
	 * special about this. The Thread.interrupt() just sets a boolean flag that the
	 * running thread then periodically checks via calls to Thread.interrupted(). We could
	 * implement this manually but it's simpler to use the built-in mechanism.
	 */
	public final void run() {
		boolean run = true;
		while(run) {
			run = simulateAndReport();
		}
	}

	protected boolean simulateAndReport() {
		try {
			// The trace simulation method should do appropriately frequent interruption
			// checks.
			globalTraceCnt = this.statistics.collectPreTrace();
			final Optional<SimulationWorkerError> res = simulateRandomTrace();
			traceCnt++;

			// If we have an error result, place it on the output queue.
			if (res.isPresent()) {
				final SimulationWorkerError err = res.get();
				resultQueue.put(SimulationWorkerResult.Error(this.myGetId(), err));
				// One would assume to return from this branch to stop the worker from creating
				// additional behaviors. However, this is at the discretion of Simulator, which
				// checks if the user ran simulation with "-continue".  If not, Simulator
				// will signal termination asynchronously.
			}

			// Abide by the maximum trace generation count.
			if (traceCnt >= maxTraceNum) {
				resultQueue.put(SimulationWorkerResult.OK(this.myGetId()));
				return false;
			}
			return true;
		} catch (final InterruptedException e) {
			// Gracefully terminate if we were interrupted.
			resultQueue.offer(SimulationWorkerResult.OK(this.myGetId()));
			return false;
		} catch (final Exception e) {
			final SimulationWorkerError err = new SimulationWorkerError(0, null, this.curState, this.getTrace(), e);
			resultQueue.offer(SimulationWorkerResult.Error(this.myGetId(), err));
			return false;
		}	
	}

	/**
	 * Check to see if the worker thread has been interrupted.
	 */
	private final void checkForInterrupt() throws InterruptedException {
		// MAK 07/2021: This used to be a call to Thread.interrupted instead of the
		// explicit stopped flag. The former doesn't work anymore because of
		// SingleThreadedSimulator (with STS, checkForTermination is called from
		// the main thread and not from the worker thread, causing workers to never
		// throw the InterruptedException, thus terminate).
		// Initially, I tried tried to change Thread.interrupted to the instance-method
		// isInterrupted, which seemed safe because checkForInterrupt is a private final
		// instance-method.  However, this only worked on Linux and macOS with a JVM
		// >= 14.
		if (Thread.interrupted() || stopped) {
			throw new InterruptedException();
		}
	}

	public final void setStopped() {
		stopped = true;
	}

	private volatile boolean stopped = false;
	
	/**
	 * This method returns a state that is randomly chosen from the set of states.
	 * It returns null if the set of states is empty.
	 */
	private final TLCState randomState(RandomGenerator rng, StateVec states) {
		final int len = states.size();
		if (len > 0) {
			final int index = (int) Math.floor(rng.nextDouble() * len);
			return states.elementAt(index);
		}
		return null;
	}
	
	@Override
	public Object setElement(final TLCState s) {
		this.nextStates.clear();
		this.nextStates.addElement(s);
		return this;
	}

	@Override
	public Object addElement(final TLCState s, final Action a, final TLCState t) {
	    if (coverage) { a.cm.incInvocations(); }

		// Any check below may terminate simulation, which then makes state the final
		// state in the trace. To correctly print its state number, it needs to know its
		// predecessor.
		t.setPredecessor(s).setAction(a);
		
		this.statistics.collectPreSuccessor(s, a, t);

		if (!tool.isGoodState(t)) {
			final Set<OpDeclNode> unassigned = t.getUnassigned();
			final String[] parameters;
			if (this.tool.getActions().length == 1) {
				parameters = new String[] { unassigned.size() > 1 ? "s are" : " is",
								unassigned.stream().map(n -> n.getName().toString())
										.collect(Collectors.joining(", ")) };
			} else {
				parameters = new String[] { a.getName().toString(),
								unassigned.size() > 1 ? "s are" : " is",
								unassigned.stream().map(n -> n.getName().toString())
										.collect(Collectors.joining(", ")) };
			}

			throw new SimulationWorkerError(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT, parameters, t, getTrace());
		}

		// Check invariants.
		int idx = 0;
		try {
			for (idx = 0; idx < this.tool.getInvariants().length; idx++) {
				if (!tool.isValid(this.tool.getInvariants()[idx], t)) {
					// We get here because of an invariant violation.
					throw new SimulationWorkerError(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR,
							new String[] { tool.getInvNames()[idx] }, t, getTrace());
				}
			}
		} catch (final Exception e) {
			if (e instanceof SimulationWorkerError) {
				throw e;
			}
			throw new SimulationWorkerError(EC.TLC_INVARIANT_EVALUATION_FAILED,
					new String[] { tool.getInvNames()[idx], e.getMessage() }, t, getTrace());
		}

		// Check action properties.
		try {
			for (idx = 0; idx < this.tool.getImpliedActions().length; idx++) {
				if (!tool.isValid(this.tool.getImpliedActions()[idx], curState, t)) {
					// We get here because of implied-action violation.
					throw new SimulationWorkerError(EC.TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR,
							new String[] { tool.getImpliedActNames()[idx] }, t, getTrace());
				}
			}
		} catch (final Exception e) {
			if (e instanceof SimulationWorkerError) {
				throw e;
			}
			throw new SimulationWorkerError(EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED,
					new String[] { tool.getImpliedActNames()[idx], e.getMessage() }, t, getTrace());
		}
		
		if ((tool.isInModel(t) && tool.isInActions(s, t))) {
			if (coverage) {	a.cm.incSecondary(); }
			return nextStates.addElement(t);
		}

		return this;
	}
	
	@Override
	public boolean hasStates() {
		assert Tool.isProbabilistic();
		return !nextStates.isEmpty();
	}
	
	@Override
    public SetOfStates getStates() {
		return new SetOfStates(nextStates);
	}

	private final StateVec nextStates = new StateVec(1);
	
	protected int getNextActionIndex(RandomGenerator rng, Action[] actions, TLCState curState) {
		return (int) Math.floor(this.localRng.nextDouble() * actions.length);
	}
	
	protected int getNextActionAltIndex(final int index, final int p, final Action[] actions, final TLCState curState) {
		return (index + p) % actions.length;
	}

	/**
	 * Generates a single random trace.
	 *
	 * The core steps of this process are as follows:
	 * 
	 *  a) Pick one of the initial states. 
	 *  b) Randomly pick an action to generate the successor states (more than 1) to the current initial state. 
	 *  c) Check all of the generated successors for their validity. 
	 *  d) Randomly pick a generated successor and make it the new current state.
	 *
	 * Returns an Optional error representing the outcome of the trace generation. If the trace generation produced no error,
	 * returns Optional.empty().
	 *
	 */
	private Optional<SimulationWorkerError> simulateRandomTrace() throws Exception {

		// a) Randomly select a state from the set of init states.
		curState = randomState(this.localRng, initStates);
		setCurrentState(curState);
		
		final Action[] actions = this.tool.getActions();
		final int len = actions.length;

		// Simulate a trace up to the maximum specified length.
		for (int traceIdx = 0; traceIdx < maxTraceDepth; traceIdx++) {
			// We don't want this thread to run for too long without checking for
			// interruption, so we do so on every iteration of the main trace generation
			// loop.
			checkForInterrupt();

			// b) Get the current state's successor states.
			nextStates.clear();
			int index = getNextActionIndex(this.localRng, actions, curState);
			final int p = this.localRng.nextPrime();
			for (int i = 0; i < len; i++) {
				try {
					this.tool.getNextStates(this, curState, actions[index]);
				} catch (SimulationWorkerError swe) {
					// getNextState doesn't throw SWE unless SimulationWorker#addElement above throws it.
					return Optional.of(swe);
				}
				if (!nextStates.empty()) {
					break;
				}
				index = getNextActionAltIndex(index, p, actions, curState);
			}
			if (nextStates.empty()) {
				if (checkDeadlock) {
					// We get here because of deadlock.
					return Optional.of(new SimulationWorkerError(EC.TLC_DEADLOCK_REACHED, null, curState, getTrace(), null));
				}
				break;
			}

			// At this point all generated successor states have been checked for
			// their respective validity (isGood/isValid/impliedActions/...).

			// d) Randomly select one of them and make it the current state for the next
			// iteration of the loop.
			final TLCState s1 = randomState(localRng, nextStates);
			
			// Execute callable on the state that was selected from the set of successor
			// states.  See TLCExt!TLCDefer operator for context.
			s1.execCallable();
			
			statistics.collectPostSuccessor(curState, actions[index], s1);
			
			curState = s1;
			setCurrentState(curState);
		}

		// Check for interruption once more before entering liveness checking.
		checkForInterrupt();

		// Check if the current trace satisfies liveness properties.
		liveCheck.checkTrace(tool.noDebug(), new Supplier<StateVec>() {
			@Override
			public StateVec get() {
				// Pass a supplier instead of the trace directly to convert
				// the linked list TLCStateMutExt <- TLCStateMutExt to an array
				// iff liveness checking is enabled.
				return getTrace();
			}
		});
		
		this.statistics.collectPostTrace(curState);
		
		// Write the trace out if desired. The trace is printed in the
		// format of TLA module, so that it can be read by TLC again.
		if (traceFile != null) {
			// Make sure each worker outputs to its own set of trace files.
			final String fileName = traceFile + "_" + String.valueOf(this.myGetId()) + "_" + this.traceCnt;
			// TODO is it ok here?
			final PrintWriter pw = new PrintWriter(FileUtil.newBFOS(fileName));
			pw.println("---------------- MODULE " + fileName + " -----------------");
			final StateVec stateTrace = new Supplier<StateVec>() {
				@Override
				public StateVec get() {
					return getTrace();
				}
			}.get();
			for (int idx = 0; idx < stateTrace .size(); idx++) {
				Action curAction = stateTrace.elementAt(idx).getAction();
				if (curAction != null) {
					pw.println("\\* " + curAction.getLocation());
				}
				pw.println("STATE_" + (idx + 1) + " == ");
				pw.println(stateTrace.elementAt(idx) + "\n");
			}
			pw.println("=================================================");
			pw.close();
		}

		postTrace(curState);
		
		// Finished trace generation without any errors.
		return Optional.empty();
	}
	
	protected boolean postTrace(final TLCState finalState) throws FileNotFoundException {
		return true;
	}
	
	public final long getTraceCnt() {
		return this.traceCnt + 1; // +1 to account for the currently generated behavior. 
	}
	
	public final StateVec getTrace() {
		return getTrace(curState);
	}

	public synchronized final StateVec getTrace(TLCState s) {
		if (s == null) {
			return new StateVec(0);
		}

		final int level = s.getLevel();
		final TLCState[] t = new TLCState[level];

		for (int i = level - 1; i >= 0; i--) {
			t[i] = s;
			s = s.getPredecessor();
		}
		assert t[0] != null && s == null;
		
		return new StateVec(t);
	}
	
	public final TLCStateInfo[] getTraceInfo(final int level) {
		final StateVec stateTrace = getTrace();
		assert 0 < level && level <= stateTrace.size();
		final TLCStateInfo[] trace = new TLCStateInfo[level];
		for (int i = 0; i < trace.length; i++) {
			final TLCState s = stateTrace.elementAt(i);
			trace[i] = new TLCStateInfo(s);
		}
		return trace;
	}

	public void setInitialStates(StateVec initStates) {
		this.initStates = initStates;
	}
	
	public void start(StateVec initStates) {
		setInitialStates(initStates);
		this.start();
	}
	
	public final RandomGenerator getRNG() {
		return this.localRng;
	}
}