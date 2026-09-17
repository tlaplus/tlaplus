/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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
package tlc2.tool.queue;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import gov.nasa.jpf.Config;
import gov.nasa.jpf.vm.AllRunnablesSyncPolicy;
import gov.nasa.jpf.vm.ApplicationContext;
import gov.nasa.jpf.vm.ChoiceGenerator;
import gov.nasa.jpf.vm.ElementInfo;
import gov.nasa.jpf.vm.GlobalSchedulingPoint;
import gov.nasa.jpf.vm.ThreadInfo;
import gov.nasa.jpf.vm.choice.ThreadChoiceFromSet;

/**
 * Adds spurious wakeups to JPF's scheduling choices.
 * <p>
 * The relevant JPF thread-state transitions are:
 * <pre>
 * lifecycle:       NEW -> RUNNING -> TERMINATED
 * lock contention: RUNNING -> BLOCKED -> UNBLOCKED -> RUNNING
 * notified wait:   RUNNING -> WAITING -> NOTIFIED -> UNBLOCKED -> RUNNING
 * timed wait:      RUNNING -> TIMEOUT_WAITING -> TIMEDOUT -> RUNNING
 * notified timeout:
 *                  TIMEOUT_WAITING -> NOTIFIED -> UNBLOCKED -> RUNNING
 * </pre>
 * This policy models a spurious wakeup by changing an untimed waiter to a
 * timeout-capable waiter. JPF then applies its normal timeout transition only
 * if that thread is actually selected to run:
 * {@code WAITING -> TIMEOUT_WAITING -> TIMEDOUT -> RUNNING}.
 */
public class SpuriousWakeupSyncPolicy extends AllRunnablesSyncPolicy {

	/**
	 * Creates the scheduler policy from the settings of the current JPF run.
	 */
	public SpuriousWakeupSyncPolicy(final Config config) {
		super(config);
	}

	/**
	 * Returns whether JPF may simulate this waiting thread waking up without
	 * another thread notifying it.
	 */
	private static boolean isWakeable(final ThreadInfo ti) {
		if (ti.getState() != ThreadInfo.State.WAITING || ti.getLockCount() == 0) {
			return false;
		}
		final ElementInfo ei = ti.getLockObject();
		return ei != null && ei.canLock(ti);
	}

	/**
	 * Builds the set of threads JPF may run next, adding threads eligible for a
	 * simulated spurious wakeup to the choices supplied by the default policy.
	 */
	@Override
	protected ThreadInfo[] getTimeoutRunnables(final ApplicationContext appCtx) {
		final List<ThreadInfo> choices = new ArrayList<ThreadInfo>(
				Arrays.asList(super.getTimeoutRunnables(appCtx)));
		for (final ThreadInfo ti : vm.getThreadList().getThreads()) {
			if (isWakeable(ti)) {
				choices.add(ti);
			}
		}
		return choices.toArray(new ThreadInfo[choices.size()]);
	}

	/**
	 * Gives JPF a scheduling choice when multiple threads can run, including
	 * waiting threads that this policy may wake spuriously.
	 */
	@Override
	protected ChoiceGenerator<ThreadInfo> getRunnableCG(final String id, final ThreadInfo tiCurrent) {
		final ApplicationContext appCtx = tiCurrent.getApplicationContext();
		final ThreadInfo[] choices = getTimeoutRunnables(appCtx);

		if (choices.length == 0) {
			return null;
		}
		if (choices.length == 1 && choices[0] == tiCurrent && !tiCurrent.isTimeoutWaiting()
				&& !isWakeable(tiCurrent) && !breakSingleChoice) {
			return null;
		}

		final ChoiceGenerator<ThreadInfo> cg = new SpuriousWakeup(id, choices);
		if (!vm.getThreadList().hasProcessTimeoutRunnables(appCtx)) {
			GlobalSchedulingPoint.setGlobal(cg);
		}
		return cg;
	}

	private static final class SpuriousWakeup extends ThreadChoiceFromSet {

		/**
		 * Records the threads from which JPF will choose the next one to run.
		 */
		private SpuriousWakeup(final String id, final ThreadInfo[] choices) {
			super(id, choices, true);
		}

		/**
		 * Advances to JPF's next scheduling choice and makes a chosen untimed
		 * waiter eligible for a simulated timeout. JPF changes it to
		 * {@code TIMEDOUT} only if it is subsequently selected to run, which
		 * keeps other waiters in a valid non-runnable state.
		 */
		@Override
		public void advance() {
			super.advance();
			final ThreadInfo ti = getNextChoice();
			if (ti != null && isWakeable(ti)) {
				ti.setState(ThreadInfo.State.TIMEOUT_WAITING);
			}
		}
	}
}
