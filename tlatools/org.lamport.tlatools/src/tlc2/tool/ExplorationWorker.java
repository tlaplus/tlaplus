/*******************************************************************************
 * Copyright (c) 2025 NVIDIA Corp. All rights reserved. 
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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool;

import java.util.Optional;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.LongAdder;
import java.util.function.Supplier;

import tlc2.output.EC;
import tlc2.tool.SimulationWorker.SimulationWorkerError;
import tlc2.tool.liveness.ILiveCheck;

public class ExplorationWorker extends SimulationWorker {

	public ExplorationWorker(int id, ITool tool, BlockingQueue<SimulationWorkerResult> resultQueue, long seed,
			int maxTraceDepth, long maxTraceNum, String traceActions, boolean checkDeadlock, String traceFile,
			ILiveCheck liveCheck, LongAdder numOfGenStates, AtomicLong numOfGenTraces, AtomicLong m2AndMean) {
		super(id, tool, resultQueue, seed, maxTraceDepth, maxTraceNum, traceActions, checkDeadlock, traceFile,
				liveCheck, numOfGenStates, numOfGenTraces, m2AndMean);
	}

	@Override
	protected Optional<SimulationWorkerError> simulateRandomTrace() throws Exception {
		// a) Randomly select a state from the (remaining) set of init states.
		curState = randomState(this.localRng, initStates);
		setCurrentState(curState);

		// This loop is a deoptimization from SimuationWorker; Instead of generating
		// all successor states (Next), SW randomly select a subaction of Next and
		// generates only the successor states of that subaction. It then randomly
		// selects one of those successor states.

		// Simulate a trace up to the maximum specified length.
		for (int traceIdx = 0; traceIdx < maxTraceDepth; traceIdx++) {
			// We don't want this thread to run for too long without checking for
			// interruption, so we do so on every iteration of the main trace generation
			// loop.
			checkForInterrupt();

			// b) Get the current state's successor states.
			nextStates.clear();

			try {
				this.tool.getNextStates(this, curState);
			} catch (SimulationWorkerError swe) {
				// getNextState doesn't throw SWE unless SimulationWorker#addElement above
				// throws it.
				return Optional.of(swe);
			}

			if (nextStates.isEmpty()) {
				if (checkDeadlock) {
					// We get here because of deadlock.
					return Optional.of(
							new SimulationWorkerError(EC.TLC_DEADLOCK_REACHED, null, getTrace(this.curState), null));
				}
				break;
			}

			// At this point all generated successor states have been checked for
			// their respective validity (isGood/isValid/impliedActions/...).

			// d) Randomly select one of them and make it the current state for the next
			// iteration of the loop.
			final TLCState s1 = randomState(localRng, nextStates);

			// Execute callable on the state that was selected from the set of successor
			// states. See TLCExt!TLCDefer operator for context.
			s1.execCallable();

			statistics.collectPostSuccessor(curState, s1.getAction(), s1);

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
				return getTrace(ExplorationWorker.this.curState);
			}
		});

		this.statistics.collectPostTrace(curState);

		postTrace(curState);

		// Finished trace generation without any errors.
		return Optional.empty();
	}
}
