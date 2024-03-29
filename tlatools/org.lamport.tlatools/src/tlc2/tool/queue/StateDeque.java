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
package tlc2.tool.queue;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.Deque;

import tlc2.tool.TLCState;

public class StateDeque extends StateQueue {
	
	private final Deque<TLCState> q;
	
	public StateDeque() {
		this.q = new ArrayDeque<>();
	}

	@Override
	void enqueueInner(final TLCState state) {
		this.q.addFirst(state);
	}

	@Override
	TLCState dequeueInner() {
		return this.q.poll();
	}

	@Override
	TLCState peekInner() {
		return this.q.peek();
	}

	@Override
	public void commitChkpt() throws IOException {
		beginChkpt();
	}

	@Override
	public void recover() throws IOException {
		beginChkpt();
	}

	@Override
	public void beginChkpt() throws IOException {
		throw new UnsupportedOperationException("StateDeque does not support checkpointing.");
	}
}
