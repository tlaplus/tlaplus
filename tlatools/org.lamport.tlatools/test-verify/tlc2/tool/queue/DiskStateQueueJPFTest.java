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

/** Checks the real queue and pool threads with in-memory pool files. */
public class DiskStateQueueJPFTest extends TestJPF {

	/** Keep spilling reachable. */
	private static final int BUF_SIZE = 2;

	private static final int WORKERS = 1;

	private static final int ENQUEUES = BUF_SIZE + 1;

	@Test
	public void testDeadlockFreedom() throws InterruptedException {
		if (verifyDeadlock("+vm.scheduler.sync.class=tlc2.tool.queue.SpuriousWakeupSyncPolicy",
				"+test.report.console.finished=result,statistics,error")) {

			// Set before DiskStateQueue initialization.
			System.setProperty("tlc2.tool.queue.DiskStateQueue.BufSize", Integer.toString(BUF_SIZE));

			TLCGlobals.setNumWorkers(WORKERS);

			final TLCState state = new DummyTLCState();
			final DiskStateQueue queue = new DiskStateQueue("pool");

			final List<Thread> threads = new ArrayList<Thread>(WORKERS + 1);
			for (int i = 0; i < WORKERS; i++) {
				threads.add(new Thread(new Worker(queue, state), "Worker" + i));
			}
			threads.add(new Thread(new Suspend(queue), "Suspend"));
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

	private static final class Worker implements Runnable {

		private final IStateQueue queue;
		private final TLCState state;

		private Worker(final IStateQueue queue, final TLCState state) {
			this.queue = queue;
			this.state = state;
		}

		@Override
		public void run() {
			for (int i = 0; i < ENQUEUES; i++) {
				this.queue.sEnqueue(this.state);
			}
			while (this.queue.sDequeue() != null) {
			}
			this.queue.finishAll();
		}
	}

	private static final class Suspend implements Runnable {

		private final DiskStateQueue queue;

		private Suspend(final DiskStateQueue queue) {
			this.queue = queue;
		}

		@Override
		public void run() {
			// Checkpoint file operations add no synchronization and are out of scope.
			if (this.queue.suspendAll()) {
				this.queue.resumeAll();
			}
		}
	}
}
