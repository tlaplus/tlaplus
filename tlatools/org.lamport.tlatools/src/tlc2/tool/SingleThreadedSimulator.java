/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved. 
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

import java.io.IOException;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.SimulationWorker.SimulationWorkerError;
import tlc2.tool.SimulationWorker.SimulationWorkerResult;
import tlc2.tool.liveness.LiveException;
import tlc2.util.RandomGenerator;
import tlc2.value.RandomEnumerableValues;
import util.Assert.TLCRuntimeException;
import util.FilenameToStream;

public class SingleThreadedSimulator extends Simulator {

	/*
	 * This Simulator is single-threaded whereas Simulator spawns multiple workers
	 * from which it consumes results. While Simulator consumes results, its workers
	 * continue with state-space exploration. Contrary, the SingleThreadedSimulator
	 * halts state-space exploration while it consumes the result of its worker.
	 * This translates into calling simulateAndReport directly as opposed to
	 * creating proper thread in Simulator. The need for SingleThreadedSimulator
	 * arose in the scope of the TLC debugger that must halt state-space
	 * exploration. Otherwise, concurrent workers mess up the stack in
	 * TLCDebugger#stack when a user e.g. debugs an Alias that is evaluated in
	 * printBehavior below. TODO: Simulator should be refactored to support the
	 * debugger use-case right away. However, I couldn't make this work for N
	 * workers without complex concurrency primitives such as a TransferQueue,
	 * Phaser, ...
	 */
	public SingleThreadedSimulator(ITool tool, String metadir, String traceFile, boolean deadlock, int traceDepth,
			long traceNum, boolean traceActions, RandomGenerator rng, long seed, FilenameToStream resolver) throws IOException {
		super(tool, metadir, traceFile, deadlock, traceDepth, traceNum, traceActions, rng, seed, resolver, 1);
	}

	@Override
	protected int simulate(final StateVec initialStates) throws InterruptedException {
		// Unless REV#reset is issued below, running simulation under the debugger will
		// result in different error traces even under identical seeds. This would not
		// necessarily be a bug but producing the same trace with and without the
		// debugger provides a better user experience. The underlying technical issue is
		// because the REV instance is thread-local, i.e., each SimulationWorker
		// maintains its own instance. The main thread generates the initial states
		// without the debugger, while a SimulationWorker generates the
		// successor/next-states. With the debugger, the main thread generates both the
		// initial- and the next-states. Thus, we reset the REV after generating the
		// initial states.
		RandomEnumerableValues.reset();
		
		final SimulationWorker simulationWorker = workers.get(0);
		simulationWorker.setInitialStates(initialStates);

		int errorCode = EC.NO_ERROR;

		while (true) {
			simulationWorker.simulateAndReport();
			if (workerResultQueue.isEmpty()) {
				continue;
			}
			final SimulationWorkerResult result = workerResultQueue.take();

			// If the result is an error, print it.
			if (result.isError()) {
				SimulationWorkerError error = result.error();

				// We assume that if a worker threw an unexpected exception, there is a bug
				// somewhere, so we print out the exception and terminate. In the case of a
				// liveness error, which is reported as an exception, we also terminate.
				if (error.exception != null) {
					if (error.exception instanceof LiveException) {
						// In case of a liveness error, there is no need to print out
						// the behavior since the liveness checker should take care of that itself.
						this.printSummary();
						errorCode = ((LiveException) error.exception).errorCode;
					} else if (error.exception instanceof TLCRuntimeException) {
						final TLCRuntimeException exception = (TLCRuntimeException) error.exception;
						printBehavior(exception, error.state, error.stateTrace);
						errorCode = exception.errorCode;
					} else {
						printBehavior(EC.GENERAL, new String[] { MP.ECGeneralMsg("", error.exception) }, error.state,
								error.stateTrace);
						errorCode = EC.GENERAL;
					}
					return errorCode;
				}

				// Print the trace for all other errors.
				printBehavior(error);

				if (isNonContinuableError(error.errorCode)) {
					return error.errorCode;
				}

				// If the 'continue' option is false, then we always terminate on the
				// first error, shutting down all workers. Otherwise, we continue receiving
				// results from the worker threads.
				if (!TLCGlobals.continuation) {
					return error.errorCode;
				}

				if (errorCode == EC.NO_ERROR) {
					errorCode = EC.GENERAL;
				}
			}
			// If the result is OK, this indicates that the worker has terminated and also
			// terminate. For example, the worker has generated the requested number of traces.
			else {
				return errorCode;
			}
		}
	}
}
