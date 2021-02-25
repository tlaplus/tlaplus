/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved.
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
 *   Ian Morris Nieves - added support for fingerprint stack trace
 ******************************************************************************/

package tlc2.value;

import java.util.Random;

import tlc2.TLCGlobals;
import tlc2.tool.ModelChecker;
import tlc2.tool.TLCState;
import tlc2.util.IdThread;

public abstract class RandomEnumerableValues {
	
	/* Randomization for sets */
		
	private static long randomSeed; 
	
	public static long getSeed() {
		return randomSeed;
	}
	
	/**
	 * Initialize Random with the given seed value.
	 **/
	public static void setSeed(final long seed) {
		randomSeed = seed;
		reset();
	}
	
	/**
	 * Re-Initialize Random with the recorded seed value.
	 * 
	 * @return The previously used Random instance that can later be re-activate
	 *         with {@link RandomEnumerableValues#set(Random)}.
	 **/
	public static Random reset() {
		final Random random = get();
		RANDOMS.remove();
		return random;
	}

	public static Random set(Random random) {
		final Random old = get();
		RANDOMS.set(random);
		return old;
	}
	
	public static Random get() {
		return RANDOMS.get();
	}
	
	private static final ThreadLocal<Random> RANDOMS = new ThreadLocal<Random>() {
		@Override
		protected Random initialValue() {
			if (TLCGlobals.mainChecker != null && ModelChecker.class.equals(TLCGlobals.mainChecker.getClass())) {
				// In order to recreate the error trace in BFS mode - which essentially
				// corresponds to rerunning state exploration following a given path - we have
				// to recreate the same random values too. Otherwise, TLC will fail to recreate
				// the trace because the recreated TLCState does not match the fingerprint in
				// the error trace/path. Therefore, we maintain one RNG per IdThread (IWorker)
				// which - for the initial states - is seeded with enumFractionSeed and - in the
				// scope of next-state - gets seeded with the fingerprint of the predecessor
				// state.
				return new TLCStateRandom(randomSeed);
			} else {
				// DFS or Simulation need no special handling because:
				// - DFS does not re-create the error trace (just prints the current trace).
				// - Simulation mode is intended to allow users to gather statistics on
				// behaviors generated with specified probabilities of different transitions.
				// (For example, to find the expected time for a message to be delivered with
				// retransmission as a function of the probability of message loss). For this,
				// it's important that the random choice have no correlation with the state in
				// which the choice is made.
				return new DefaultRandom(randomSeed);
			}
		}

		@Override
		public Random get() {
			// Hook to re-initialize random (no-op for DFS and simulation).
			return ((EnumerableValueRandom) super.get()).initialize();
		}
	};
		
	private interface EnumerableValueRandom {
		Random initialize();
	}

	@SuppressWarnings("serial")
	private static final class DefaultRandom extends Random implements EnumerableValueRandom {
		public DefaultRandom(long randomSeed) {
			super(randomSeed);
		}

		@Override
		public final Random initialize() {
			// Noop
			return this;
		}
	}

	@SuppressWarnings("serial")
	private static final class TLCStateRandom extends Random implements EnumerableValueRandom {

		private TLCState state;

		public TLCStateRandom(long randomSeed) {
			super(randomSeed);
		}

		private void initializedFor(final TLCState state) {
			// XOR the state's fingerprint with the initial randomSeed value. This is done
			// so that two identical states (same fingerprint) of two different
			// specifications do not produce the same random value.
			final long seed = state.fingerPrint() ^ randomSeed;
			this.setSeed(seed);
			this.state = state;
		}

		private boolean isInitializedFor(final TLCState another) {
			return state == another;
		}

		@Override
		public Random initialize() {
			final TLCState state = IdThread.getCurrentState();
			// state is null during the generation of initial states and non-null in the
			// scope of the next-state relation (however, state can be an initial state).
			// Thus, an RNG is seeded with randomSeed during the generation of initial
			// states and seeded with randomSeed ^ predecessor's fingerprint during the
			// generation of next states.
			// Do not re-initialize random for the same TLCState twice to produce two
			// distinct values with high probability with a next-state such as:
			// Next == x' = RandomElement(0..2) /\ y' = RandomElement(0..2)
			// If random was to be re-initialized/re-seeded, RandomElement(0..2) for x' and y'
			// would be identical values (also see tlc2.tool.RandomElementXandYTest).
			if (state != null && !isInitializedFor(state)) {
				initializedFor(state);
			}
			return this;
		}
	}
}
