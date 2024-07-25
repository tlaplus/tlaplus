/*******************************************************************************
 * Copyright (c) 2024 Microsoft Research. All rights reserved.
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

import static org.junit.Assert.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CountDownLatch;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.tool.queue.IStateQueue;
import tlc2.tool.queue.MemStateQueue;
import tlc2.value.impl.IntValue;

public class Github971cTest extends ModelCheckerTestCase {

	public Github971cTest() {
		super("Github971", new String[] { "-lncheck", "off", "-config", "Github971c.cfg" }, EC.ExitStatus.VIOLATION_SAFETY);
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}

	@Override
	protected boolean runWithDebugger() {
		return false;
	}

	@Override
	protected boolean doDump() {
		return false;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Test
	public void testSpec() throws IOException {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));

		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "3"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "13", "4", "0"));

		// Assert it has found the temporal violation and also a counter example
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertTrue(recorder.recorded(EC.TLC_COUNTER_EXAMPLE));

		// Assert the error trace.
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT2));
		final List<String> expectedTrace = new ArrayList<String>(3);
		expectedTrace.add("x = -1");
		expectedTrace.add("x = 1");
		expectedTrace.add("x = 0");
		assertTraceWith(recorder.getRecords(EC.TLC_STATE_PRINT2), expectedTrace);
	}

	@Override
	protected int getNumberOfThreads() {
		// Has to be >1 to reproduce the race condition.
		return 2;
	}

	@Override
	protected void beforeSetUp() {
		try {
			IStateQueue.Factory.sq = new IStateQueue() {
				private final CountDownLatch signal = new CountDownLatch(4);

				private final IStateQueue inner = new MemStateQueue();

				public void sEnqueue(TLCState state) {
					inner.sEnqueue(state);

					if (IntValue.ValZero.equals(state.lookup("x"))) {
						try {
							// t1 gets blocked so that t2 gets ahead.
							signal.await();
						} catch (InterruptedException e) {
							e.printStackTrace();
						}
					}
				}

				public TLCState sDequeue() {
					signal.countDown();
					return inner.sDequeue();
				}

				public void enqueue(TLCState state) {
					inner.enqueue(state);
				}

				public TLCState dequeue() {
					return inner.dequeue();
				}

				public void sEnqueue(TLCState[] states) {
					inner.sEnqueue(states);
				}

				public void sEnqueue(StateVec stateVec) {
					inner.sEnqueue(stateVec);
				}

				public TLCState sPeek() {
					return inner.sPeek();
				}

				public TLCState[] sDequeue(int cnt) {
					return inner.sDequeue(cnt);
				}

				public void finishAll() {
					inner.finishAll();
				}

				public boolean suspendAll() {
					return inner.suspendAll();
				}

				public void resumeAll() {
					inner.resumeAll();
				}

				public void resumeAllStuck() {
					inner.resumeAllStuck();
				}

				public long size() {
					return inner.size();
				}

				public void beginChkpt() throws IOException {
					inner.beginChkpt();
				}

				public void commitChkpt() throws IOException {
					inner.commitChkpt();
				}

				public void recover() throws IOException {
					inner.recover();
				}

				public boolean isEmpty() {
					return inner.isEmpty();
				}

				public void delete() throws IOException {
					inner.delete();
				}
			};
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
