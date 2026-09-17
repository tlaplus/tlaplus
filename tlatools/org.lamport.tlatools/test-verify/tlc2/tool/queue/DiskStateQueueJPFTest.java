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
import java.util.List;

import org.junit.Test;

import gov.nasa.jpf.util.test.TestJPF;
import tlc2.TLCGlobals;
import tlc2.tool.TLCState;

/**
 * Checks the real queue and pool threads with in-memory pool files. Unlike
 * {@link StateQueueJPFTest}, this test cannot substitute storage in a subclass:
 * {@link DiskStateQueue}'s concrete storage hooks and pool threads are the
 * behavior under test. The modeled streams keep file state in JPF's backtrackable
 * heap; real filesystem state would not be restored when JPF backtracks.
 */
public class DiskStateQueueJPFTest extends TestJPF {

	/** Keep spilling reachable. */
	private static final int BUF_SIZE = 1;

	private static final int WORKERS = 1;

	private static final int ENQUEUES = BUF_SIZE + 1;

	private static final class DistinctDummyTLCState extends DummyTLCState {

		private DistinctDummyTLCState() {
			super();
		}

		private DistinctDummyTLCState(final long fp) {
			super(fp);
		}

		@Override
		public TLCState createEmpty() {
			// Avoid artificial JPF interleavings caused by aliasing deserialized states.
			return new DistinctDummyTLCState(0L);
		}
	}

	@Test
	public void testDeadlockFreedom() throws InterruptedException {
		if (verifyDeadlock(
				// Avoid choices when references are first published; monitor synchronization remains explored.
				"+vm.shared.break_on_exposure=false",
				"+test.report.console.finished=result,statistics,error")) {
	
			// Set before DiskStateQueue initialization.
			System.setProperty("tlc2.tool.queue.DiskStateQueue.BufSize", Integer.toString(BUF_SIZE));

			TLCGlobals.setNumWorkers(WORKERS);

			final TLCState state = new DistinctDummyTLCState();
			final DiskStateQueue queue = new DiskStateQueue("pool");
			queue.enqueue(state);

			final List<Thread> threads = new ArrayList<>();
			final TLCState[] states = new TLCState[ENQUEUES];
			// Avoid artificial interleavings related to shared state instances in JPF.
			for (int i = 0; i < states.length; i++) {
				states[i] = new DistinctDummyTLCState(i + 1L);
			}
			for (int i = 0; i < WORKERS; i++) {
				threads.add(new Thread(new WorkerTask(1, queue, states), "Worker" + i));
			}
			threads.add(new Thread(new MainTask(queue), "Suspend"));
			for (final Thread thread : threads) {
				thread.start();
			}
			for (final Thread thread : threads) {
				thread.join();
			}
			queue.writer.join();
			assert !queue.writer.isAlive();
		}
	}

}
