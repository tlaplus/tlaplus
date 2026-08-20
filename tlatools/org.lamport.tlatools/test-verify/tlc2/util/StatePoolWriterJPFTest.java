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
package tlc2.util;

import java.io.File;

import org.junit.After;
import org.junit.Test;

import gov.nasa.jpf.util.test.TestJPF;
import tlc2.tool.TLCState;

/**
 * Uses JPF to exhaustively explore the interleavings of the
 * {@code DiskStateQueue} pool-writer protocol, i.e. the three call sites of
 * {@link StatePoolWriter} that TLC's worker and main threads reach
 * concurrently:
 * <ul>
 * <li>{@link StatePoolWriter#doWork(TLCState[], File)} from
 * {@code DiskStateQueue.enqueueInner}, when a worker spills {@code enqBuf},
 * <li>{@link StatePoolWriter#ensureWritten()} from
 * {@code DiskStateQueue.fillDeqBuffer}, when a worker refills {@code deqBuf},
 * and
 * <li>the argument-less {@code writer.notifyAll()} in
 * {@code DiskStateQueue.finishAll()}.
 * </ul>
 * <p>
 * {@code finishAll} is not only called once all workers are done. A single
 * worker calls it as soon as it hits an error (see
 * {@code ModelChecker.doNextSetErr} and the {@code Throwable} handler in
 * {@code Worker.run}), while the remaining workers keep generating states.
 * Its {@code notifyAll()} therefore reaches the writer as an <em>empty
 * wake</em>: the writer is notified although {@code poolFile} is still
 * {@code null}.
 * <p>
 * {@link StatePoolWriter#run()} treats such an empty wake as a shutdown signal
 * and returns. The next spill then leaves a worker blocked in
 * {@code ensureWritten()} forever, and because {@code fillDeqBuffer} runs
 * under the {@code DiskStateQueue} monitor, every other worker piles up behind
 * it and TLC hangs.
 * <p>
 * JPF reports this as a deadlock via its {@code NotDeadlockedProperty}. JPF
 * does not model spurious wakeups, so reaching the deadlock requires nothing
 * but an unlucky schedule of the three threads below.
 * <p>
 * See <a href="https://github.com/tlaplus/tlaplus/issues/1403">#1403</a>.
 */
public class StatePoolWriterJPFTest extends TestJPF {

	/**
	 * A zero-length buffer keeps the state serialization out of the explored
	 * interleavings; the defect is in the writer's wait/notify protocol, not in
	 * how it serializes states.
	 */
	private static final int BUF_SIZE = 0;

	private static final String POOL_FILE = "statepool.jpf.tmp";

	public static void main(final String[] args) {
		new StatePoolWriterJPFTest().testWriterMustSurviveEmptyWake();
	}

	/**
	 * JPF's {@code java.io} model writes through to the host file system, so the
	 * interleavings in which the writer does its job leave the pool file behind.
	 * This runs in the host VM, not under JPF.
	 */
	@After
	public void deletePoolFile() {
		new File(POOL_FILE).delete();
	}

	@Test
	public void testWriterMustSurviveEmptyWake() {
		if (verifyNoPropertyViolation()) {
			// Mirrors how DiskStateQueue's constructor starts the writer.
			final StatePoolWriter writer = new StatePoolWriter(BUF_SIZE);
			writer.setDaemon(true);
			writer.start();

			// Mirrors DiskStateQueue.finishAll() being called by the one worker
			// that hit an error while the others keep running.
			final Thread finisher = new Thread(new Finisher(writer), "Finisher");
			// Mirrors a worker that spills enqBuf and later refills deqBuf.
			final Thread spiller = new Thread(new Spiller(writer), "Spiller");

			finisher.start();
			spiller.start();

			try {
				finisher.join();
				spiller.join();
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			}
		}
	}

	private static class Finisher implements Runnable {
		private final StatePoolWriter writer;

		Finisher(final StatePoolWriter writer) {
			this.writer = writer;
		}

		@Override
		public void run() {
			synchronized (this.writer) {
				this.writer.notifyAll();
			}
		}
	}

	private static class Spiller implements Runnable {
		private final StatePoolWriter writer;

		Spiller(final StatePoolWriter writer) {
			this.writer = writer;
		}

		@Override
		public void run() {
			try {
				this.writer.doWork(new TLCState[BUF_SIZE], new File(POOL_FILE));
				this.writer.ensureWritten();
			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			} catch (final Exception e) {
				assert false : "Unexpected exception: " + e;
			}
		}
	}
}
