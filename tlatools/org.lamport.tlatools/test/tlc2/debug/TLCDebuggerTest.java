/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved. 
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
package tlc2.debug;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.StackTraceArguments;
import org.junit.Test;

public class TLCDebuggerTest {

	@Test
	public void testStackFrameWhileRunning() throws InterruptedException, ExecutionException {
		// Debugger returns no stack frames when execution is not halted.
		assertEquals(0, new TestTLCDebugger(20, false).getFrames().size());
	}

	@Test
	public void testStackFramePaginationEmpty() throws InterruptedException, ExecutionException {
		assertEquals(0, new TestTLCDebugger().getFrames(new StackTraceArguments()).size());
	}

	@Test
	public void testStackFramePaginationEmpty2() throws InterruptedException, ExecutionException {
		assertEquals(0, new TestTLCDebugger().getFrames(new TestStackTraceArguments(null, 20)).size());
	}

	@Test
	public void testStackFramePaginationEmpty3() throws InterruptedException, ExecutionException {
		assertEquals(0, new TestTLCDebugger().getFrames(new TestStackTraceArguments(20, null)).size());
	}

	@Test
	public void testStackFramePaginationEmpty4() throws InterruptedException, ExecutionException {
		assertEquals(0, new TestTLCDebugger().getFrames(new TestStackTraceArguments(20, 20)).size());
	}

	@Test
	public void testStackFramePaginationEmpty5() throws InterruptedException, ExecutionException {
		assertEquals(0, new TestTLCDebugger().getFrames(new TestStackTraceArguments(-20, null)).size());
	}

	@Test
	public void testStackFramePaginationEmpty6() throws InterruptedException, ExecutionException {
		assertEquals(0, new TestTLCDebugger().getFrames(new TestStackTraceArguments(null, -20)).size());
	}

	@Test
	public void testStackFramePaginationEmpty7() throws InterruptedException, ExecutionException {
		assertEquals(0, new TestTLCDebugger().getFrames(new TestStackTraceArguments(-20, -20)).size());
	}

	// *************************** End Empty *************************** //

	@Test
	public void testStackFramePaginationLevelNull() throws InterruptedException, ExecutionException {
		assertEquals(1, new TestTLCDebugger(new TLCStackFrame(0)).getFrames(new StackTraceArguments()).size());
	}

	@Test
	public void testStackFramePaginationLevel0() throws InterruptedException, ExecutionException {
		// null and 0 map to all frames.
		assertEquals(1,
				new TestTLCDebugger(new TLCStackFrame(0)).getFrames(new TestStackTraceArguments(null, 0)).size());
		assertEquals(1,
				new TestTLCDebugger(new TLCStackFrame(0)).getFrames(new TestStackTraceArguments(null, null)).size());
	}

	@Test
	public void testStackFramePaginationStartFrame0() throws InterruptedException, ExecutionException {
		assertEquals(1,
				new TestTLCDebugger(new TLCStackFrame(0)).getFrames(new TestStackTraceArguments(0, null)).size());
		assertEquals(1,
				new TestTLCDebugger(new TLCStackFrame(0)).getFrames(new TestStackTraceArguments(null, null)).size());
	}

	@Test
	public void testStackFramePaginationStartFrame1() throws InterruptedException, ExecutionException {
		assertEquals(0,
				new TestTLCDebugger(new TLCStackFrame(0)).getFrames(new TestStackTraceArguments(1, null)).size());
	}

	@Test
	public void testStackFramePaginationStartFrameNegative() throws InterruptedException, ExecutionException {
		assertEquals(0,
				new TestTLCDebugger(new TLCStackFrame(0)).getFrames(new TestStackTraceArguments(-1, null)).size());
	}

	// *************************** End One Frame *************************** //

	@Test
	public void testStackFramePagination() throws InterruptedException, ExecutionException {
		final List<StackFrame> frames = new TestTLCDebugger(20).getFrames();
		assertEquals(20, frames.size());

		Collections.reverse(frames); // Re-reverse to make loop simpler.
		for (int i = 0; i < frames.size(); i++) {
			assertEquals(i, frames.get(i).getId());
		}
	}

	@Test
	public void testStackFramePaginationsStartFrame1() throws InterruptedException, ExecutionException {
		List<StackFrame> frames = new TestTLCDebugger(20).getFrames(new TestStackTraceArguments(1, null));
		assertEquals(19, frames.size());

		Collections.reverse(frames); // Re-reverse to make loop simpler.
		for (int i = 0; i < frames.size(); i++) {
			assertEquals(i, frames.get(i).getId());
		}
	}

	@Test
	public void testStackFramePaginationsStartFrameSubList() throws InterruptedException, ExecutionException {
		int start = 5;
		List<StackFrame> frames = new TestTLCDebugger(20).getFrames(new TestStackTraceArguments(start, 5));
		assertEquals(5, frames.size());

		assertEquals(14, frames.get(0).getId());
		assertEquals(13, frames.get(1).getId());
		assertEquals(12, frames.get(2).getId());
		assertEquals(11, frames.get(3).getId());
		assertEquals(10, frames.get(4).getId());
	}

	@Test
	public void testStackFramePaginationsStartFrameOutOfRange() throws InterruptedException, ExecutionException {
		assertEquals(0, new TestTLCDebugger(20).getFrames(new TestStackTraceArguments(20, null)).size());
	}

	// *************************** Helpers *************************** //

	protected class TestTLCDebugger extends TLCDebugger {
		public TestTLCDebugger() {
			super(Step.In, true, true);
		}

		public TestTLCDebugger(TLCStackFrame tlcStackFrame) {
			super(Step.In, true, true);
			this.stack.add(tlcStackFrame);
		}

		public TestTLCDebugger(List<TLCStackFrame> frames) {
			super(Step.In, true, true);
			this.stack.addAll(frames);
		}

		public TestTLCDebugger(int n) {
			this(n, true);
		}
		
		public TestTLCDebugger(int n, boolean executionIsHalted) {
			super(Step.In, true, executionIsHalted);
			this.stack.addAll(IntStream.range(0, n).boxed().sorted(Collections.reverseOrder())
					.map(i -> new TestTLCStackFrame(i)).collect(Collectors.toList()));
		}

		public List<StackFrame> getFrames() throws InterruptedException, ExecutionException {
			return Arrays.asList(stackTrace(new TestStackTraceArguments()).get().getStackFrames());
		}

		public List<StackFrame> getFrames(StackTraceArguments sta) throws InterruptedException, ExecutionException {
			return Arrays.asList(stackTrace(sta).get().getStackFrames());
		}
	}

	protected class TestTLCStackFrame extends TLCStackFrame {

		public TestTLCStackFrame(int id) {
			super(id);
		}

		@Override
		public String toString() {
			return "TLCStackFrame [id=" + getId() + "]";
		}
	}

	protected class TestStackTraceArguments extends StackTraceArguments {
		public TestStackTraceArguments() {
			super();
		}

		public TestStackTraceArguments(Integer start, Integer level) {
			super();
			setStartFrame(start);
			setLevels(level);
		}
	}
}
