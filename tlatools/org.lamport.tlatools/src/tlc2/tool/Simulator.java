// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2023, Oracle and/or its affiliates.
// Last modified on Mon 30 Apr 2007 at 15:29:56 PST by lamport
//      modified on Thu Jan 10 11:22:26 PST 2002 by yuanyu

package tlc2.tool;

import java.io.IOException;
import java.math.BigDecimal;
import java.math.RoundingMode;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.TimerTask;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.LongAdder;
import java.util.stream.Collectors;

import tla2sany.semantic.ExprNode;
import tla2sany.st.Location;
import tlc2.TLCGlobals;
import tlc2.module.TLCGetSet;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.StatePrinter;
import tlc2.tool.SimulationWorker.SimulationWorkerError;
import tlc2.tool.SimulationWorker.SimulationWorkerResult;
import tlc2.tool.SimulationWorker.SimulationWorkerStatistics;
import tlc2.tool.coverage.CostModelCreator;
import tlc2.tool.impl.FastTool;
import tlc2.tool.impl.Tool;
import tlc2.tool.liveness.ILiveCheck;
import tlc2.tool.liveness.LiveCheck;
import tlc2.tool.liveness.LiveCheck1;
import tlc2.tool.liveness.LiveException;
import tlc2.tool.liveness.NoOpLiveCheck;
import tlc2.util.DotActionWriter;
import tlc2.util.IdThread;
import tlc2.util.RandomGenerator;
import tlc2.util.Vect;
import tlc2.util.statistics.DummyBucketStatistics;
import tlc2.value.IValue;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.CounterExample;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.Value;
import util.Assert.TLCRuntimeException;
import util.FileUtil;
import util.FilenameToStream;
import util.UniqueString;

public class Simulator {

	public static boolean EXTENDED_STATISTICS = Boolean
			.getBoolean(Simulator.class.getName() + ".extendedStatistics");
	public static boolean EXTENDED_STATISTICS_NAIVE = Boolean
			.getBoolean(Simulator.class.getName() + ".extendedStatistics.naive");
	public static boolean EXPERIMENTAL_LIVENESS_SIMULATION = Boolean
			.getBoolean(Simulator.class.getName() + ".experimentalLiveness");
	private final String traceActions;
	private final Value config;

	/* Constructors */

	// SZ Feb 20, 2009: added the possibility to pass the SpecObject
	public Simulator(String specFile, String configFile, String traceFile, boolean deadlock, int traceDepth,
			long traceNum, RandomGenerator rng, long seed, FilenameToStream resolver,
			int numWorkers) throws IOException {
		this(new FastTool(extracted(specFile), configFile, resolver, Tool.Mode.Simulation, new HashMap<>()), "", traceFile, deadlock,
				traceDepth, traceNum, null, rng, seed, resolver, numWorkers);
	}

	private static String extracted(String specFile) {
		int lastSep = specFile.lastIndexOf(FileUtil.separatorChar);
		return specFile.substring(lastSep + 1);
	}

	public Simulator(ITool tool, String metadir, String traceFile, boolean deadlock, int traceDepth,
				long traceNum, String traceActions, RandomGenerator rng, long seed, FilenameToStream resolver,
				int numWorkers) throws IOException {
		this.tool = tool;

		this.checkDeadlock = deadlock && tool.getModelConfig().getCheckDeadlock();
		this.checkLiveness = !tool.livenessIsTrue();
		this.invariants = tool.getInvariants();
		if (traceDepth != -1) {
			// this.actionTrace = new Action[traceDepth]; // SZ: never read
			// locally
			this.traceDepth = traceDepth;
		} else {
			// this.actionTrace = new Action[0]; // SZ: never read locally
			this.traceDepth = Integer.MAX_VALUE;
		}
		this.traceFile = traceFile;
		this.traceNum = traceNum;
		this.traceActions = traceActions;
		this.rng = rng;
		this.seed = seed;
		this.aril = 0;

		ILiveCheck liveCheck = new NoOpLiveCheck(tool, metadir);
		final AtomicBoolean errorFound = new AtomicBoolean(false);
		this.numWorkers = numWorkers;
		this.workers = new ArrayList<>(numWorkers);
		for (int i = 0; i < this.numWorkers; i++) {
			// Minimize thread contention by not sharing (real) ILiveCheck instances among workers.
			if (this.checkLiveness) {
				if (EXPERIMENTAL_LIVENESS_SIMULATION) {
					final String tmpDir = Files.createTempDirectory(String.format("tlc-simulator-%s-", i)).toString();
					liveCheck = new LiveCheck(tool.noDebug(), tmpDir, new DummyBucketStatistics());
				} else {
					liveCheck = new LiveCheck1(tool.noDebug(), errorFound, i != 0);
				}
			}
			
			final ITool t = i == 0 ? tool : tool.noDebug();
			if (Boolean.getBoolean(Simulator.class.getName() + ".rl")) {
				this.workers.add(new RLSimulationWorker(i, t, this.workerResultQueue, this.rng.nextLong(),
						this.traceDepth, this.traceNum, this.traceActions, this.checkDeadlock, this.traceFile,
						liveCheck, this.numOfGenStates, this.numOfGenTraces, this.welfordM2AndMean));
			} else if (Boolean.getBoolean(Simulator.class.getName() + ".rlaction")) {
				this.workers.add(new RLActionSimulationWorker(i, t, this.workerResultQueue, this.rng.nextLong(),
						this.traceDepth, this.traceNum, this.traceActions, this.checkDeadlock, this.traceFile,
						liveCheck, this.numOfGenStates, this.numOfGenTraces, this.welfordM2AndMean));
			} else {
				this.workers.add(new SimulationWorker(i, t, this.workerResultQueue, this.rng.nextLong(),
						this.traceDepth, this.traceNum, this.traceActions, this.checkDeadlock, this.traceFile,
						liveCheck, this.numOfGenStates, this.numOfGenTraces, this.welfordM2AndMean));
			}
		}
	
		// Eagerly create the config value in case the next-state relation involves
		// TLCGet("config"). In this case, we would end up locking the
		// UniqueString#InternTable for every lookup. See AbstractChecker too.
		this.config = createConfig();
		
		if (TLCGlobals.isCoverageEnabled() || TLCGlobals.Coverage.isEnabled()) {
        	CostModelCreator.create(this.tool);
        }
		
		//TODO Eventually derive Simulator from AbstractChecker.
		AbstractChecker.scheduleTermination(new TimerTask() {
			@Override
			public void run() {
				Simulator.this.stop();
			}
		});
	}

	/* Fields */
	private final ITool tool;
	private final Action[] invariants; // the invariants to be checked
	private final boolean checkDeadlock; // check deadlock?
	private final boolean checkLiveness; // check liveness?

	// The total number of states/traces generated by all workers. May be written to
	// concurrently, so we use a LongAdder to reduce potential contention.
	private final LongAdder numOfGenStates = new LongAdder();
	private final AtomicLong numOfGenTraces = new AtomicLong();
	private final AtomicLong welfordM2AndMean = new AtomicLong();

	// private Action[] actionTrace; // SZ: never read locally
	private final String traceFile;

	// The maximum length of a simulated trace.
	private final int traceDepth;

	// The maximum number of total traces to generate.
	private final long traceNum;

	// The number of worker threads to use for simulation.
	private int numWorkers = 1;

	private final RandomGenerator rng;
	private final long seed;
	private long aril;

	// Each simulation worker pushes their results onto this shared queue.
	protected final BlockingQueue<SimulationWorkerResult> workerResultQueue = new LinkedBlockingQueue<>();
	
    /**
     * Timestamp of when simulation started.
     */
	private final long startTime = System.currentTimeMillis();
	
	protected final List<SimulationWorker> workers;
		 
	 /**
	 * Returns whether a given error code is considered "continuable". That is, if
	 * any worker returns this error, should we consider continuing to run the
	 * simulator. These errors are considered "fatal" since they most likely
	 * indicate an error in the way the spec is written.
	 */
	protected boolean isNonContinuableError(int ec) {
		return ec == EC.TLC_INVARIANT_EVALUATION_FAILED || 
			   ec == EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED ||
			   ec == EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT;
	}
	
	/**
	 * Shut down all of the given workers and make sure they have stopped.
	 */
	private void shutdownAndJoinWorkers(final List<SimulationWorker> workers) throws InterruptedException {
		// Do not wait indefinitely for other workers to terminate gracefully. Instead,
		// forcefully terminate them if they do not shut down within 10 seconds.
		// 
		// For example, if a worker prints a counterexample and then calls
		// `shutdownAndJoinWorkers` to stop the other workers, TLC should not
		// wait too long. This prevents delays when workers take an extended time to
		// generate successor states for a particular action (a disjunct of the
		// next-state relation), such as an action like \E n \in 1..10000000: x' = n.
		for (SimulationWorker worker : workers) {
			// First signal all workers...
			worker.interrupt();
		}
		for (SimulationWorker worker : workers) {
			// ... and then wait for all workers.
			worker.join(10_000L);
		}
	}

	/*
	 * This method does random simulation on a TLA+ spec.
	 * 
	 * It runs until an error is encountered or we have generated the maximum number of traces.
	 * 
   * @return an error code, or <code>EC.NO_ERROR</code> on success
	 */
	public int simulate() throws Exception {
		final int res = this.tool.checkAssumptions();
		if (res != EC.NO_ERROR) {
			return res;
		}
		
		TLCState curState = null;
		//TODO: Refactor to check validity and inModel via IStateFunctor.
		final StateVec initStates;

		//
		// Compute the initial states.
		//
		try {
			// The init states are calculated only ever once and never change
			// in the loops below. Ideally the variable would be final.
			final StateVec inits = this.tool.getInitStates();
			initStates = new StateVec(inits.size());

			// This counter should always be initialized at zero.
			assert (this.numOfGenStates.longValue() == 0);
			this.numOfGenStates.add(inits.size());
			
			MP.printMessage(EC.TLC_COMPUTING_INIT_PROGRESS, this.numOfGenStates.toString());

			// Check all initial states for validity.
			for (int i = 0; i < inits.size(); i++) {
				curState = inits.elementAt(i);
				if (this.tool.isGoodState(curState)) {
					for (int j = 0; j < this.invariants.length; j++) {
						if (!this.tool.isValid(this.invariants[j], curState)) {
							// We get here because of invariant violation.
							int err = MP.printError(EC.TLC_INVARIANT_VIOLATED_INITIAL,
									new String[] { this.tool.getInvNames()[j], tool.evalAlias(curState, curState).toString() });
							tool.checkPostConditionWithCounterExample(new CounterExample(curState));
							return err;
						}
					}
				} else {
					return MP.printError(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL, curState.toString());
				}
				
				if (tool.isInModel(curState)) {
					initStates.addElement(curState);
				}
			}
		} catch (Exception e) {
			final int errorCode;
			if (curState != null) {
				errorCode = MP.printError(EC.TLC_INITIAL_STATE,
						new String[] { (e.getMessage() == null) ? e.toString() : e.getMessage(), curState.toString() });
			} else {
				errorCode = MP.printError(EC.GENERAL, e); // LL changed call 7 April 2012
			}

			this.printSummary();
			return errorCode;
		}

		if (this.numOfGenStates.longValue() == 0) {
			return MP.printError(EC.TLC_NO_STATES_SATISFYING_INIT);
		}
		if (this.numOfGenStates.longValue() > 0 && initStates.isEmpty()) {
			return MP.printError(EC.TLC_NO_STATES_SATISFYING_INIT_AND_CONSTRAINT);
		}

		MP.printMessage(EC.TLC_INIT_GENERATED1, String.valueOf(initStates.size()), "");

		// It appears deepNormalize brings the states into a canonical form to
		// speed up equality checks.
		initStates.deepNormalize();

		//
		// Start progress report thread.
		//
		final ProgressReport report = new ProgressReport();
		report.start();

		//
		// Start simulating.
		//
		this.aril = rng.getAril();
		
		int errorCode = simulate(initStates);

		// Do a final progress report.
		report.isRunning = false;
		synchronized (report) {
			report.notify();
		}
		// Wait for the progress reporter thread to finish.
		report.join();

		if (errorCode == EC.NO_ERROR) {
			// Do not print the summary again, which has already happened, e.g., when the
			// simulator printed a behavior above.
			this.printSummary();
		}
		return errorCode;
	}

	protected int simulate(final StateVec initStates) throws InterruptedException {
		// Start up multiple simulation worker threads, each with their own unique seed.
		final Set<Integer> runningWorkers = new HashSet<>();
		for (int i = 0; i < this.workers.size(); i++) {
			SimulationWorker worker = workers.get(i);
			worker.start(initStates);
			runningWorkers.add(i);
		}

		SimulationWorkerResult result;
		int errorCode = EC.NO_ERROR;
		
		// Continuously consume results from all worker threads.
		while (true) {
			result = workerResultQueue.take();

			// If the result is an error, print it.
			if (result.workerId() == -1) {
				runningWorkers.clear();
				break;
			} else if (result.isError()) {
				SimulationWorkerError error = result.error();
				
				// We assume that if a worker threw an unexpected exception, there is a bug
				// somewhere, so we print out the exception and terminate. In the case of a
				// liveness error, which is reported as an exception, we also terminate.
				if (error.exception != null) {
					if (error.exception instanceof LiveException) {
						// In case of a liveness error, there is no need to print out
						// the behavior since the liveness checker should take care of that itself.
						this.printSummary();
						error.errorCode = ((LiveException)error.exception).errorCode;
					} else if (error.exception instanceof TLCRuntimeException) {
						final TLCRuntimeException exception = (TLCRuntimeException)error.exception;
						printBehavior(exception, error.stateTrace);
						error.errorCode = exception.errorCode;
					} else {
						printBehavior(EC.GENERAL, new String[] { MP.ECGeneralMsg("", error.exception) },
								error.stateTrace);
						error.errorCode = EC.GENERAL;
					}
					errorCode = error.errorCode;
					break;
				}
				
				// Print the trace for all other errors.
				printBehavior(error);
				
				// For certain, "fatal" errors, we shut down all workers and terminate,
				// regardless of the "continue" parameter, since these errors likely indicate a bug in the spec.
				if (isNonContinuableError(error.errorCode)) {
					error.errorCode = error.errorCode;
					errorCode = error.errorCode;
					break;
				}
				
				// see tlc2.tool.Worker.doPostCheckAssumption()
				if (result.error().hasTrace()) {
					error.errorCode = Math.max(this.tool.checkPostConditionWithCounterExample(result.error().getCounterExample()), error.errorCode);
				} else {
					error.errorCode = Math.max(this.tool.checkPostCondition(), error.errorCode);
				}
				
				// If the 'continue' option is false, then we always terminate on the
				// first error, shutting down all workers. Otherwise, we continue receiving
				// results from the worker threads.
				if (!TLCGlobals.continuation) {
					error.errorCode = error.errorCode;
					errorCode = error.errorCode;
					break;
				}

				if (error.errorCode == EC.NO_ERROR)
				{
					error.errorCode = EC.GENERAL;
				}
				errorCode = error.errorCode;
			}
			// If the result is OK, this indicates that the worker has terminated, so we
			// make note of this. If all of the workers have terminated, there is no need to
			// continue waiting for results, so we should terminate.
			else {
				errorCode = this.tool.checkPostCondition();
				runningWorkers.remove(result.workerId());
				if(runningWorkers.isEmpty()) {
					break;
				}
			}
		}
		
		// Shut down all workers.
		this.shutdownAndJoinWorkers(workers);
		return errorCode;
	}

	protected final void printBehavior(final TLCRuntimeException exception, final StateVec stateTrace) {
		MP.printTLCRuntimeException(exception);
		printBehavior(stateTrace);
	}

	protected final void printBehavior(SimulationWorkerError error) {
		printBehavior(error.errorCode, error.parameters, error.stateTrace);
	}

	/**
	 * Prints out the simulation behavior, in case of an error. (unless we're at
	 * maximum depth, in which case don't!)
	 */
	protected final void printBehavior(final int errorCode, final String[] parameters, final StateVec stateTrace) {
		MP.printError(errorCode, parameters);
		printBehavior(stateTrace);
		this.printSummary();
	}
	
	private final void printBehavior(final StateVec stateTrace) {
		if (this.traceDepth == Integer.MAX_VALUE) {
			MP.printMessage(EC.TLC_ERROR_STATE);
			StatePrinter.printStandaloneErrorState(stateTrace.last());
		} else {
			MP.printError(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT);
			// MAK 09/24/2019: For space reasons, TLCState does not store the state's action.
			// This is why the loop below creates TLCStateInfo instances out of the pair cur
			// -> last to print the action's name as part of the error trace. This is
			// especially useful for Error-Trace Explorer in the Toolbox.
			TLCState lastState = null;
			TLCStateInfo sinfo;
			int omitted = 0;
			for (int i = 0; i < stateTrace.size(); i++) {
				final TLCState curState = stateTrace.elementAt(i);
				// Last state's successor is itself.
				final TLCState sucState = stateTrace.elementAt(Math.min(i + 1, stateTrace.size() - 1));
				if (lastState != null) {
					// Contrary to BFS/ModelChecker, simulation remembers the action (its id) during
					// trace exploration to print the error-trace without re-evaluating the
					// next-state relation for lastStates -> cusState (tool.getState(curState,
					// lastState)) to determine the action.  This would fail for specs whose next-state
					// relation is probabilistic (ie. TLC!RandomElement or Randomization.tla). In other
					// words, tool.getState(curState,lastState) would return for some pairs of states.
					sinfo = new TLCStateInfo(curState);
				} else {
					sinfo = new TLCStateInfo(curState);
					StatePrinter.printInvariantViolationStateTraceState(tool.evalAlias(sinfo, sucState), lastState,
							curState.getLevel(), i + 1 == stateTrace.size());
					lastState = curState;
					continue;
				}
				
				// MAK 09/25/2019: It is possible for
				// tlc2.tool.SimulationWorker.simulateRandomTrace() to produce traces with
				// *non-terminal* stuttering steps, i.e. it might produce traces such
				// as s0,s1,s1,s2,s3,s3,s3,...sN* (where sN* represents an infinite suffix of
				// "terminal" stuttering steps). In other words, it produces traces s.t.
				// a trace has finite (sub-)sequence of stuttering steps.
				// The reason is that simulateRandomTrace, with non-zero probability, selects
				// a stuttering step as the current state's successor. Guarding against it
				// would require to fingerprint states (i.e. check equality) for each selected
				// successor state (which is considered too expensive).
				// A trace with finite stuttering can be reduced to a shorter - hence
				// better readable - trace with only infinite stuttering at the end. This
				// takes mostly care of the confusing Toolbox behavior where a trace with
				// finite stuttering is silently reduced by breadth-first-search when trace
				// expressions are evaluated (see https://github.com/tlaplus/tlaplus/issues/400#issuecomment-650418597).
				if (TLCGlobals.printDiffsOnly && curState.fingerPrint() == lastState.fingerPrint()) {
					omitted++;
				} else {
					// print the state's actual level and not a monotonically increasing state
					// number => Numbering will have gaps with difftrace.
					StatePrinter.printInvariantViolationStateTraceState(tool.evalAlias(sinfo, sucState), lastState, curState.getLevel(), i + 1 == stateTrace.size());
				}
				lastState = curState;
			}
			if (omitted > 0) {
				assert TLCGlobals.printDiffsOnly;
				MP.printMessage(EC.GENERAL, String.format(
						"difftrace requested: Shortened behavior by omitting finite stuttering (%s states), which is an artifact of simulation mode.\n",
						omitted));
			}
		}
	}

	public IValue getLocalValue(int idx) {
		for (SimulationWorker w : workers) {
			return w.getLocalValue(idx);
		}
		return null;
	}

	public void setAllValues(int idx, IValue val) {
		for (SimulationWorker w : workers) {
			w.setLocalValue(idx, val);
		}
	}

	public List<IValue> getAllValues(int idx) {
		return workers.stream().map(w -> w.getLocalValue(idx)).collect(Collectors.toList());
	}
	
	public final Value getAllValues() {
		final IValue[] localValues = workers.get(0).getLocalValues();
		
		final Map<Value, Value> m = new HashMap<>(localValues.length);
		
		for (int i = 0; i < localValues.length; i++) {
			final IValue iValue = localValues[i];
			if (iValue != null) {
				final Value[] vals = new Value[workers.size()];
				for (int j = 0; j < vals.length; j++) {
					vals[j] = (Value) workers.get(j).getLocalValue(i);
				}
				m.put(IntValue.gen(i), new TupleValue(vals));
			}
		}
		return new FcnRcdValue(m);
	}


	/**
	 * Prints the summary
	 */
	protected final void printSummary() {
		this.reportCoverage();

		try {
			this.writeActionFlowGraph();
		} catch (Exception e) {
			// SZ Jul 10, 2009: changed from error to bug
			MP.printTLCBug(EC.TLC_REPORTER_DIED, null);
		}

		/*
		 * This allows the toolbox to easily display the last set of state space
		 * statistics by putting them in the same form as all other progress statistics.
		 */
		if (TLCGlobals.tool) {
			MP.printMessage(EC.TLC_PROGRESS_SIMU, String.valueOf(numOfGenStates.longValue()),
					String.valueOf(numOfGenTraces.longValue()));
		}

		MP.printMessage(EC.TLC_STATS_SIMU, new String[] { String.valueOf(numOfGenStates.longValue()),
				String.valueOf(this.seed), String.valueOf(this.aril) });
	}

	/**
	 * Reports coverage
	 */
	public final void reportCoverage() {
		if (TLCGlobals.isCoverageEnabled()) {
            CostModelCreator.report(this.tool, this.startTime);
		}
	}

	public final ITool getTool() {
	    return this.tool;	
	}
	
	/**
	 * Reports progress information
	 */
	final class ProgressReport extends Thread {

		volatile boolean isRunning = true;

		public void run() {
			final ExprNode periodic = tool.getSpecProcessor().getPeriodic();
			int count = TLCGlobals.coverageInterval / TLCGlobals.progressInterval;
			try {
				while (isRunning) {
					synchronized (this) {
						this.wait(TLCGlobals.progressInterval);
					}
					final long genTrace = numOfGenTraces.longValue();
					final long m2AndMean = welfordM2AndMean.get();
					final long mean = m2AndMean & 0x00000000FFFFFFFFL; // could be int.
					final long m2 = m2AndMean >>> 32;
					MP.printMessage(EC.TLC_PROGRESS_SIMU, 
							String.valueOf(numOfGenStates.longValue()),
							String.valueOf(genTrace),
							String.valueOf(mean),
							String.valueOf(Math.round(m2 / (genTrace + 1d))), // Var(X),  +1 to prevent div-by-zero.
							String.valueOf(Math.round(Math.sqrt(m2 / (genTrace + 1d))))); // SD, +1 to prevent div-by-zero.
					if (count > 1) {
						count--;
					} else {
						reportCoverage();
						count = TLCGlobals.coverageInterval / TLCGlobals.progressInterval;
					}

					writeActionFlowGraph();

					if (periodic != null && BoolValue.ValFalse.equals(tool.noDebug().eval(periodic))) {
						MP.printError(EC.TLC_ASSUMPTION_FALSE, periodic.toString());
						workerResultQueue.add(SimulationWorkerResult.OK(-1));
					}
				}
			} catch (Exception e) {
				// SZ Jul 10, 2009: changed from error to bug
				MP.printTLCBug(EC.TLC_REPORTER_DIED, null);
			}
		}

	}

	private void writeActionFlowGraph() throws IOException {
		if ("BASIC".equals(traceActions)) {
			writeActionFlowGraphBasic();
		} else if ("FULL".equals(traceActions)) {
			writeActionFlowGraphFull();
		}
	}
	
	private void writeActionFlowGraphFull() throws IOException {		
		// The number of actions is expected to be low (dozens commons and hundreds are
		// rare). This is why the code below isn't optimized for performance.
		final Vect<Action> initAndNext = tool.getSpecActions();
		final int len = initAndNext.size();
		
		// Clusters of actions that have the same context:
		// CONSTANT Proc
		// ...
		// A(p) == p \in {...} /\ v' = 42...
		// Next == \E p \in Proc : A(p)
		final Map<String, Set<Integer>> clusters = new HashMap<>();
		for (int i = 0; i < len; i++) {
			final String con = initAndNext.elementAt(i).con.toString();
			if (!clusters.containsKey(con)) {
				clusters.put(con, new HashSet<>());	
			}
			clusters.get(con).add(i);
		}
		
		// Write clusters to dot file (override previous file).
		final DotActionWriter dotActionWriter = new DotActionWriter(
				Simulator.this.tool.getRootName() + "_actions.dot", "");
		for (Entry<String, Set<Integer>> cluster : clusters.entrySet()) {
			// key is a unique set of chars accepted/valid as a graphviz cluster id.
			final String key = Integer.toString(Math.abs(cluster.getKey().hashCode()));
			dotActionWriter.writeSubGraphStart(key, cluster.getKey().toString());
			
			final Set<Integer> ids = cluster.getValue();
			for (Integer id : ids) {
				dotActionWriter.write(initAndNext.elementAt(id), id);
			}
			dotActionWriter.writeSubGraphEnd();
		}					
		
		// Element-wise sum the statistics from all workers.
		long[][] aggregateActionStats = new long[len][len];
		final List<SimulationWorker> workers = Simulator.this.workers;
		for (SimulationWorker sw : workers) {
			final long[][] s = sw.statistics.actionStats;
			for (int i = 0; i < len; i++) {
				for (int j = 0; j < len; j++) {
					aggregateActionStats[i][j] += s[i][j];
				}
			}
		}
		
		// Create a map from id to action name.
		final Map<Integer, Action> idToActionName = new HashMap<>();
		for (int i = 0; i < initAndNext.size(); i++) {
			Action action = initAndNext.elementAt(i);
			idToActionName.put(action.getId(), action);
		}

		// Write stats to dot file as edges between the action vertices.
		for (int i = 0; i < len; i++) {
			for (int j = 0; j < len; j++) {
				long l = aggregateActionStats[i][j];
				if (l > 0L) {
					// LogLog l (to keep the graph readable) and round to two decimal places (to not
					// write a gazillion decimal places truncated by graphviz anyway).
					final double loglogWeight = Math.log10(Math.log10(l+1)); // +1 to prevent negative inf.
					dotActionWriter.write(i, j,
							BigDecimal.valueOf(loglogWeight).setScale(2, RoundingMode.HALF_UP)
							.doubleValue());
				} else if (!idToActionName.get(j).isInitPredicate()) {
					// Only draw an unseen arc if the sink is not an initial prediate.
					dotActionWriter.write(i, j);
				}
			}
		}
		
		// Close dot file.
		dotActionWriter.close();
	}

	private void writeActionFlowGraphBasic() throws IOException {
		// The number of actions is expected to be low (dozens commons and hundreds a
		// rare). This is why the code below isn't optimized for performance.
		final Vect<Action> initAndNext = tool.getSpecActions();
		final int len = initAndNext.size();
		
		// Element-wise sum the statistics from all workers.
		long[][] aggregateActionStats = new long[len][len];
		final List<SimulationWorker> workers = Simulator.this.workers;
		for (SimulationWorker sw : workers) {
			final long[][] s = sw.statistics.actionStats;
			for (int i = 0; i < len; i++) {
				for (int j = 0; j < len; j++) {
					aggregateActionStats[i][j] += s[i][j];
				}
			}
		}
		
		// Create mappings from distinct ids to action ids and name.
		final Map<Integer, Action> idToAction = new HashMap<>();
		final Map<Location, Integer> actionToId = new HashMap<>();
		for (int i = 0; i < initAndNext.size(); i++) {
			final Action action = initAndNext.elementAt(i);
			
			if (!actionToId.containsKey(action.getDefinition())) {
				int id = idToAction.size();
				idToAction.put(id, action);
				actionToId.put(action.getDefinition(), id);
			}
		}
		final Map<Integer, Integer> actionsToDistinctActions = new HashMap<>();
		for (int i = 0; i < initAndNext.size(); i++) {
			final Action action = initAndNext.elementAt(i);
			actionsToDistinctActions.put(action.getId(), actionToId.get(action.getDefinition()));
		}
		
		// Override previous basic file.
		final DotActionWriter dotActionWriter = new DotActionWriter(
				Simulator.this.tool.getRootName() + "_actions.dot", "");

		// Identify actions in the dot file.
		idToAction.forEach((id, a) -> dotActionWriter.write(a, id));
		
		// Having the aggregated action stats, reduce it to account for only
		// the distinct action names.
		long[][] reducedAggregateActionStats = new long[idToAction.size()][idToAction.size()];
		for (int i = 0; i < len; i++) {
			// Find origin id.
			final int originActionId = actionsToDistinctActions.get(i);
			for (int j = 0; j < len; j++) {
				// Find next id.
				final int nextActionId = actionsToDistinctActions.get(j);
				reducedAggregateActionStats[originActionId][nextActionId] += aggregateActionStats[i][j];
			}
		}

		// Write stats to dot file as edges between the action vertices.
		for (int i = 0; i < idToAction.size(); i++) {
			for (int j = 0; j < idToAction.size(); j++) {
				long l = reducedAggregateActionStats[i][j];
				if (l > 0L) {
					// LogLog l (to keep the graph readable) and round to two decimal places (to not
					// write a gazillion decimal places truncated by graphviz anyway).
					final double loglogWeight = Math.abs(Math.log10(Math.log10(l + 1))); // +1 to prevent negative inf.
					dotActionWriter.write(i, j,
							BigDecimal.valueOf(loglogWeight).setScale(2, RoundingMode.HALF_UP).doubleValue());
				} else if (!idToAction.get(j).isInitPredicate()) {
					// Only draw an unseen arc if the sink is not an initial prediate.
					dotActionWriter.write(i, j);
				}
			}
		}
		
		// Close dot file.
		dotActionWriter.close();
	}

	public final StateVec getTrace(final TLCState s) {
		if (Thread.currentThread() instanceof SimulationWorker) {
			final SimulationWorker w = (SimulationWorker) Thread.currentThread();
			return w.getTrace(s);
		} else {
			assert numWorkers == 1 && workers.size() == numWorkers;
			return workers.get(0).getTrace(s);
		}
	}
	
	public void stop() {
		for (SimulationWorker worker : workers) {
			worker.setStopped();
			worker.interrupt();
		}
	}

	public RandomGenerator getRNG() {
		if (Thread.currentThread() instanceof SimulationWorker) {
			final SimulationWorker w = (SimulationWorker) Thread.currentThread();
			return w.getRNG();
		} else {
			return this.rng;
		}
	}

	public int getTraceDepth() {
		return this.traceDepth;
	}

	public final SimulationWorkerStatistics getWorkerStatistics() {
		if (Thread.currentThread() instanceof SimulationWorker) {
			final SimulationWorker w = (SimulationWorker) Thread.currentThread();
			return w.statistics;
		} else {
			return workers.get(0).statistics;
		}	
	}
	
	public final Value getStatistics(final TLCState s) {
		final UniqueString[] n = new UniqueString[11];
		final Value[] v = new Value[n.length];
		
		final long genTrace = numOfGenTraces.longValue();
		n[0] = TLCGetSet.TRACES;
		v[0] = IntValue.narrowToIntValue(genTrace);
		
		n[1] = TLCGetSet.DURATION;
		v[1] = IntValue.narrowToIntValue((System.currentTimeMillis() - startTime) / 1000L);

		n[2] = TLCGetSet.GENERATED;
		v[2] = IntValue.narrowToIntValue(numOfGenStates.longValue());

		n[3] = TLCGetSet.BEHAVIOR;
		v[3] = getWorkerStatistics().getTraceStatistics(s);

		n[4] = TLCGetSet.WORKER;
		v[4] = IntValue.gen(Thread.currentThread() instanceof IdThread ? IdThread.GetId() : 0);

		n[5] = TLCGetSet.DISTINCT;
		v[5] = getWorkerStatistics().getDistinctStates();
		
		n[6] = TLCGetSet.DISTINCT_VALUES;
		v[6] = getWorkerStatistics().getDistinctValues();
		
		n[7] = TLCGetSet.RETRIES;
		v[7] = getWorkerStatistics().getNextRetries();
		
		n[8] = TLCGetSet.SPEC_ACTIONS;
		v[8] = getWorkerStatistics().getActions();
		
		final long m2AndMean = welfordM2AndMean.get();
		final long mean = m2AndMean & 0x00000000FFFFFFFFL; // could be int.
		n[9] = TLCGetSet.LEVEL_MEAN;
		v[9] = IntValue.narrowToIntValue(mean);

		final long m2 = m2AndMean >>> 32;
		n[10] = TLCGetSet.LEVEL_VARIANCE;
		v[10] = IntValue.narrowToIntValue(Math.round(m2 / (genTrace + 1d)));// Var(X),  +1 to prevent div-by-zero.

		return new RecordValue(n, v, false);
	}

	public final Value getConfig() {
		return this.config;
	}

	private final Value createConfig() {
		final UniqueString[] n = new UniqueString[9];
		final Value[] v = new Value[n.length];
		
		n[0] = TLCGetSet.MODE;
		v[0] = Tool.isProbabilistic() ? new StringValue("generate") : new StringValue("simulate");

		n[1] = TLCGetSet.DEPTH;
		v[1] = IntValue.gen(this.traceDepth == Integer.MAX_VALUE ? -1 : this.traceDepth);

		n[2] = TLCGetSet.TRACES;
		v[2] = IntValue.gen((int) (this.numWorkers * traceNum));

		n[3] = TLCGetSet.DEADLOCK;
		v[3] = checkDeadlock ? BoolValue.ValTrue : BoolValue.ValFalse;

		n[4] = TLCGetSet.SEED;
		v[4] = new StringValue(Long.toString(seed));

		n[5] = TLCGetSet.ARIL;
		v[5] = new StringValue(Long.toString(aril));

		n[6] = TLCGetSet.WORKER;
		v[6] = IntValue.gen(numWorkers);

		n[7] = TLCGetSet.INSTALL;
		v[7] = new StringValue(TLCGlobals.getInstallLocation());

		n[8] = TLCGetSet.SCHED;
		v[8] = new StringValue(getScheduler());
		
		return new RecordValue(n, v, false);
	}
	
	private static String getScheduler() {
		if (Boolean.getBoolean(Simulator.class.getName() + ".rl")) {
			return "rl";
		} else if (Boolean.getBoolean(Simulator.class.getName() + ".rlaction")) {
			return "rlaction";
		} else {
			return "random";
		}
	}
}
