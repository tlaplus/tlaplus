/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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

import java.io.IOException;

import org.junit.Test;

import gov.nasa.jpf.util.test.TestJPF;
import tlc2.tool.TLCState;

public class StateQueueJPFTest extends TestJPF {

	@Test
	public void test() {
		if (verifyNoPropertyViolation()) {
			final StateQueue queue = new DummyStateQueue();
			final TLCState tlcState = new DummyTLCState();
			queue.enqueue(tlcState);
			
			Thread main = new Thread(new Runnable() {
				public void run() {
					queue.suspendAll();
					// critical section (taking a checkpoint)
					queue.resumeAll();
				}
			}, "Main");
			main.start();
			
			Thread worker = new Thread(new Runnable() {
				public void run() {
					for (int i = 0; i < 10; i++) {
						TLCState state = queue.dequeue();
						if (state == null) {
							queue.finishAll();
							return;
						}
						queue.enqueue(tlcState);
					}
					queue.finishAll();
				}
			}, "Worker");
			worker.start();
		}
	}
	
	/*
	 * Dummy implementation of StateQueue with minimal functionality compared to
	 * DiskStateQueue or MemStateQueue. After all, we verify the abstract
	 * StateQueue and not the implementations (which should be done separately).
	 */
	private static class DummyStateQueue extends StateQueue {

		private TLCState state;

		void enqueueInner(TLCState state) {
			this.state = state;
		}

		TLCState dequeueInner() {
			return state;
		}

		public void beginChkpt() throws IOException {
			// checkpointing not being verified
		}

		public void commitChkpt() throws IOException {
			// checkpointing not being verified
		}

		public void recover() throws IOException {
			// checkpointing not being verified
		}
	}
}
