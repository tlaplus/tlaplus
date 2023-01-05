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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.atomic.AtomicLong;
import java.util.concurrent.atomic.LongAdder;

import tlc2.tool.liveness.ILiveCheck;
import tlc2.util.RandomGenerator;

// See https://www.microsoft.com/en-us/research/uploads/prod/2019/12/QL-OOPSLA-2020.pdf

// See https://github.com/microsoft/coyote/compare/main...pdeligia/rl-fuzzing

public class RLSimulationWorker extends SimulationWorker {
	
	// Alpha = Learning Rate
	protected static final double ALPHA = Double.valueOf(System.getProperty(Simulator.class.getName() + ".rl.alpha", ".3d"));
	// Gamma = Discount factor
	protected static final double GAMMA = Double.valueOf(System.getProperty(Simulator.class.getName() + ".rl.gamma", ".7d"));
	protected static final double REWARD = Double.valueOf(System.getProperty(Simulator.class.getName() + ".rl.reward", "-10d"));

	protected final Map<Action, Map<Long, Double>> q = new HashMap<>();

	public RLSimulationWorker(int id, ITool tool, BlockingQueue<SimulationWorkerResult> resultQueue, long seed,
			int maxTraceDepth, long maxTraceNum, boolean checkDeadlock, String traceFile, ILiveCheck liveCheck) {
		this(id, tool, resultQueue, seed, maxTraceDepth, maxTraceNum, null, checkDeadlock, traceFile, liveCheck,
				new LongAdder(), new AtomicLong(), new AtomicLong());
	}
	
	public RLSimulationWorker(int id, ITool tool, BlockingQueue<SimulationWorkerResult> resultQueue, long seed,
			int maxTraceDepth, long maxTraceNum, String traceActions, boolean checkDeadlock, String traceFile,
			ILiveCheck liveCheck, LongAdder numOfGenStates, AtomicLong numOfGenTraces, AtomicLong m2AndMean) {
		super(id, tool, resultQueue, seed, maxTraceDepth, maxTraceNum, traceActions, checkDeadlock, traceFile, liveCheck,
				numOfGenStates, numOfGenTraces, m2AndMean);
		
		for (final Action a : tool.getActions()) {
			q.put(a, new HashMap<>());
		}
	}
	
	protected double getReward(final long fp, final Action a) {
		// The reward is negative to force RL to find alternative solutions instead of
		// finding the best (one) solution over again. For example, in a maze, RL would
		// be rewarded +1 if it makes it to the exit. Here, we want to find other paths
		// elsewhere.
		return REWARD;
		// TODO Experiment with other rewards. 
	}
	
	private final double getMaxQ(final long fp) {
		double max = -Double.MAX_VALUE;
		for (Action a : q.keySet()) {
			// Map#get instead of Map#getOrDefaults causes an NPE in max when the fp is unknown.
			double d = this.q.get(a).getOrDefault(fp, -Double.MAX_VALUE);
			max = Math.max(max, d);
		}
		return max;
	}
	
	protected long getHash(TLCState state) {
		return state.fingerPrint();
	}
	
	@Override
	protected int getNextActionAltIndex(final int index, final int p, final Action[] actions, final TLCState curState) {
		// Action at state is not enabled.
		this.q.get(actions[index]).put(getHash(curState), -Double.MAX_VALUE);
		return super.getNextActionAltIndex(index, p, actions, curState);
	}
	
	@Override
	protected final int getNextActionIndex(final RandomGenerator rng, final Action[] actions, final TLCState state) {
		final long s = getHash(state);
		
		// TODO Experiment with initializing to other values. 
		this.q.values().forEach(m -> m.putIfAbsent(s, 0d));
		
		// Calculate the sum over all actions.
		double denum = 0; 
		double[] d = new double[actions.length];
		for (int i = 0; i < d.length; i++) {
			d[i] = Math.exp(this.q.get(actions[i]).get(s));
			denum += d[i];
		}		
		
// Apache commons-math with its Pair impl can replace the rest of this method. 
// However, TLC does not come with commons-math.
//		final List<Pair<Integer, Double>> arr = new ArrayList<>(d.length);
//		for (int i = 0; i < d.length; i++) {
//			arr.add(new Pair<>(i, d[i] / denum));
//		}
//		
//		return new EnumeratedDistribution<>(arr).sample();
		
		// Calculate the individual weight.
		final ArrayList<Pair> m = new ArrayList<>(d.length);
		for (int i = 0; i < d.length; i++) {
			m.add(new Pair(i, d[i] / denum));
		}

		final double nd = rng.nextDouble();

		// Sort m and calculate the cumulative weights.
		java.util.Collections.sort(m);
		for (int i = 0; i < d.length; i++) {
			final Pair p = m.get(i);
			d[i] = i == 0 ? p.key : d[i - 1] + p.key;

			// Preemptively exit if the cumulative weight exceeds
			// the uniformly chosen nd at random.
			if (d[i] >= nd) {
				return p.value;
			}
		}
		// Fallback for issues with double precision above.
		return m.get(d.length - 1).value;
	}
	
	@Override
	protected boolean postTrace(TLCState s) {
		final int level = s.getLevel();
		for (int i = level - 1; i > 0; i--) {
			final double maxQ = getMaxQ(getHash(s));
			
			final TLCState p = s.getPredecessor();
			final long fp = getHash(p);
			
			final Action ai = s.getAction();
			
			final double qi = this.q.get(ai).get(fp);
			final double q = ((1d - ALPHA) * qi) + (ALPHA * (getReward(fp, ai) + (GAMMA * maxQ)));
			
			this.q.get(ai).put(fp, q);
			
			s = p;
		}
		return true;
	}
	
	private static class Pair implements Comparable<Pair> {
		public final double key;
		public final int value;

		public Pair(int v, double k) {
			key = k;
			value = v;
		}

		@Override
		public int compareTo(Pair o) {
			return Double.compare(o.key, key);
		}

		@Override
		public String toString() {
			return "[key=" + key + ", value=" + value + "]";
		}
	}
}
