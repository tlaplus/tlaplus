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
 ******************************************************************************/
package tlc2.tool.queue;

import tlc2.tool.TLCState;

final class WorkerTask implements Runnable {

	private final int iterations;
	private final StateQueue queue;
	private final TLCState[] states;

	WorkerTask(final StateQueue queue, final TLCState... states) {
		this.iterations = 3;
		this.queue = queue;
		this.states = states;
	}

	WorkerTask(final int iterations, final StateQueue queue, final TLCState... states) {
		this.iterations = iterations;
		this.queue = queue;
		this.states = states;
	}

	@Override
	public void run() {
		for (int i = 0; i < iterations; i++) {
			final TLCState state = this.queue.sDequeue();
			if (state == null) {
				this.queue.finishAll();
				return;
			}
			this.queue.sEnqueue(this.states);
		}
		this.queue.finishAll();
	}
}
