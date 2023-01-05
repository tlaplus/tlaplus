/*******************************************************************************
 * Copyright (c) 2022 Microsoft Research. All rights reserved. 
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

import java.util.concurrent.BlockingQueue;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.LongAdder;

import tlc2.tool.liveness.ILiveCheck;

public class RLActionSimulationWorker extends RLSimulationWorker {
	
	public RLActionSimulationWorker(int id, ITool tool, BlockingQueue<SimulationWorkerResult> resultQueue, long seed,
			int maxTraceDepth, long maxTraceNum, String traceActions, boolean checkDeadlock, String traceFile,
			ILiveCheck liveCheck, LongAdder numOfGenStates, AtomicLong numOfGenTraces, AtomicLong m2AndMean) {
		super(id, tool, resultQueue, seed, maxTraceDepth, maxTraceNum, traceActions, checkDeadlock, traceFile, liveCheck,
				numOfGenStates, numOfGenTraces, m2AndMean);
	}
	
	@Override
	protected long getHash(final TLCState state) {
		return state.getAction().hashCode();
	}

	@Override
	protected int getNextActionAltIndex(final int index, final int p, final Action[] actions, final TLCState state) {
		// Action at state is not enabled; assign a negative weight/reward.
		this.q.get(actions[index]).put(getHash(state), ALPHA * (getReward(getHash(state), actions[index])));
		return super.getNextActionAltIndex(index, p, actions, state);
	}
	
	@Override
	protected boolean postTrace(TLCState s) {
		// no-op
		return true;
	}
}
