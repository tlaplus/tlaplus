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

/** Adds spurious wakeups to JPF's scheduling choices. */
public class SpuriousWakeupSyncPolicy extends AllRunnablesSyncPolicy {

	public SpuriousWakeupSyncPolicy(final Config config) {
		super(config);
	}

	private static boolean isWakeable(final ThreadInfo ti) {
		if (ti.getState() != ThreadInfo.State.WAITING || ti.getLockCount() == 0) {
			return false;
		}
		final ElementInfo ei = ti.getLockObject();
		return ei != null && ei.canLock(ti);
	}

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

		private SpuriousWakeup(final String id, final ThreadInfo[] choices) {
			super(id, choices, true);
		}

		@Override
		public void advance() {
			super.advance();
			final ThreadInfo ti = getNextChoice();
			if (ti != null && isWakeable(ti)) {
				ti.setState(ThreadInfo.State.TIMEDOUT);
			}
		}
	}
}
