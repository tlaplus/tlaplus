/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.Phaser;

import org.eclipse.lsp4j.debug.ContinueArguments;
import org.eclipse.lsp4j.debug.NextArguments;
import org.eclipse.lsp4j.debug.SetBreakpointsArguments;
import org.eclipse.lsp4j.debug.Source;
import org.eclipse.lsp4j.debug.SourceBreakpoint;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.StackTraceArguments;
import org.eclipse.lsp4j.debug.StepInArguments;
import org.eclipse.lsp4j.debug.StepOutArguments;
import org.eclipse.lsp4j.debug.StoppedEventArguments;
import org.eclipse.lsp4j.debug.services.IDebugProtocolClient;
import org.eclipse.lsp4j.jsonrpc.Launcher;
import org.eclipse.lsp4j.jsonrpc.RemoteEndpoint;
import org.junit.Before;

import tla2sany.semantic.OpDeclNode;
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.util.Context;

public abstract class TLCDebuggerTestCase extends ModelCheckerTestCase implements IDebugProtocolClient {

	protected final TestTLCDebugger debugger = new TestTLCDebugger();
	protected final Phaser phase = new Phaser();

	public TLCDebuggerTestCase(String spec, String path, final int exitStatus,
			final SetBreakpointsArguments initialBreakpoint) {
		super(spec, path, new String[] { "-debugger" }, exitStatus);

		// (i) This/current/control/test thread and (ii) executor thread that runs TLC
		// and is launched in setUp below.
		phase.bulkRegister(2);

		// Register debugger and add a breakpoint *before* TLC gets started in setUp.
		TLCDebugger.Factory.OVERRIDE = debugger;
		debugger.setBreakpoints(initialBreakpoint);
	}

	@Override
	protected boolean noGenerateSpec() {
		return !super.noGenerateSpec();
	}

	@Override
	protected boolean doCoverage() {
		// We consider coverage to be orthogonal to debugging for now although coverage
		// will be relevant during debugging a spec.
		return !super.doCoverage();
	}

	@Before
	@Override
	public void setUp() {
		// Run TLC in another thread. Control TLC through the debugger from this thread.
		Executors.newSingleThreadExecutor().submit(() -> {
			super.setUp();
			// Model-checking has ended at this point, resume the control/test thread for
			// the unit test to terminate.
			phase.arrive();
		});

		// The debugger always stops at the initial frame (usually this is the spec's
		// first ASSUMPTIONS). After advance, the bootstrapping is done and the actual
		// test can start.
		phase.arriveAndAwaitAdvance();
	}

	protected static SetBreakpointsArguments createBreakpointArgument(final String spec, final int line) {
		final SetBreakpointsArguments arguments = new SetBreakpointsArguments();
		final SourceBreakpoint breakpoint = new SourceBreakpoint();
		breakpoint.setLine(line);
		final SourceBreakpoint[] breakpoints = new SourceBreakpoint[] { breakpoint };
		arguments.setBreakpoints(breakpoints);
		final Source source = new Source();
		source.setName(spec);
		arguments.setSource(source);
		return arguments;
	}

	protected static void assertTLCNextFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec, final OpDeclNode... unassigned) {
		assertTLCNextFrame(stackFrame, beginLine, endLine, spec, Context.Empty, unassigned);
	}

	protected static void assertTLCNextFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec, final Context expectedContext, final OpDeclNode... unassigned) {
		assertTLCFrame(stackFrame, beginLine, endLine, expectedContext, spec);

		assertTrue(stackFrame instanceof TLCNextStackFrame);
		final TLCNextStackFrame f = (TLCNextStackFrame) stackFrame;

		assertTrue(Arrays.asList(f.getScopes()).stream().filter(s -> TLCNextStackFrame.SCOPE.equals(s.getName()))
				.findAny().isPresent());

		assertNotNull(f.predecessor);
		assertTrue(f.predecessor.allAssigned());

		assertTrue(f.nestedVariables.isEmpty());

		assertNotNull(f.state);
		assertEquals(new HashSet<>(Arrays.asList(unassigned)), f.state.getUnassigned());
	}

	protected static void assertTLCInitFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec) {
		assertTLCInitFrame(stackFrame, beginLine, endLine, spec, new OpDeclNode[0]);
	}

	protected static void assertTLCInitFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec, final OpDeclNode... unassigned) {
		assertTLCInitFrame(stackFrame, beginLine, endLine, spec, Context.Empty, unassigned);
	}

	protected static void assertTLCInitFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec, final Context expectedContext, final OpDeclNode... unassigned) {
		assertTLCFrame(stackFrame, beginLine, endLine, expectedContext, spec);

		assertTrue(stackFrame instanceof TLCInitStackFrame);
		final TLCInitStackFrame f = (TLCInitStackFrame) stackFrame;

		assertEquals(expectedContext, f.getContext());

		assertTrue(Arrays.asList(f.getScopes()).stream().filter(s -> TLCInitStackFrame.SCOPE.equals(s.getName()))
				.findAny().isPresent());

		assertTrue(f.nestedVariables.isEmpty());

		assertNotNull(f.state);

		assertEquals(new HashSet<>(Arrays.asList(unassigned)), f.state.getUnassigned());
	}

	protected static void assertTLCFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec) {
		assertTLCFrame(stackFrame, beginLine, endLine, Context.Empty, spec);
	}

	protected static void assertTLCFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			final Context expectedContext, String spec) {
		assertNotNull(stackFrame);
		assertEquals(beginLine, stackFrame.getLine());
		assertEquals(endLine, (int) stackFrame.getEndLine());
		assertEquals(spec, stackFrame.getSource().getName());
		assertTrue(stackFrame instanceof TLCStackFrame);
		final TLCStackFrame f = (TLCStackFrame) stackFrame;

		assertEquals(0, new ContextComparator().compare(expectedContext, f.getContext()));

		final boolean present = Arrays.asList(f.getScopes()).stream()
				.filter(s -> TLCStackFrame.SCOPE.equals(s.getName())).findAny().isPresent();
		if (expectedContext == Context.Empty) {
			assertFalse(present);
		} else {
			assertTrue(present);
		}
	}

	@Override
	public void stopped(StoppedEventArguments args) {
		// The executor/TLC thread calls this stop method.
		phase.arriveAndAwaitAdvance();
	}

	protected static class ContextComparator implements Comparator<Context> {

		@Override
		public int compare(Context o1, Context o2) {
			if (o1 == o2) {
				return 0;
			}
			while (o1.hasNext()) {
				//TODO: Compare Context#name too!
				if (!o1.getValue().equals(o2.getValue())) {
					return -1;
				}
				o1 = o1.next();
				o2 = o2.next();
			}
			return o1.hasNext() == o2.hasNext() ? 0 : -1;
		}
	}

	protected class TestTLCDebugger extends TLCDebugger {

		public void setBreakpoints(final String rootModule, int line) {
			setBreakpoints(createBreakpointArgument(rootModule, line));
		}

		public void unsetBreakpoints() {
			// Convenience methods
			final SetBreakpointsArguments args = new SetBreakpointsArguments();
			args.setBreakpoints(new SourceBreakpoint[0]);
			setBreakpoints(args);
		}

		public StackFrame[] stackTrace() throws Exception {
			// Convenience methods
			return stackTrace(new StackTraceArguments()).get().getStackFrames();
		}

		public StackFrame[] next() throws Exception {
			// Convenience methods
			next(new NextArguments()).whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
			return stackTrace();
		}

		public StackFrame[] stepOut() throws Exception {
			// Convenience methods
			stepOut(new StepOutArguments()).whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
			return stackTrace();
		}

		public StackFrame[] stepIn() throws Exception {
			// Convenience methods
			stepIn(new StepInArguments()).whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
			return stackTrace();
		}

		public StackFrame[] continue_() throws Exception {
			// Convenience methods
			continue_(new ContinueArguments()).whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
			return stackTrace();
		}

		public class TestLauncher implements Launcher<IDebugProtocolClient> {

			@Override
			public IDebugProtocolClient getRemoteProxy() {
				return TLCDebuggerTestCase.this;
			}

			@Override
			public RemoteEndpoint getRemoteEndpoint() {
				return null;
			}

			@Override
			public Future<Void> startListening() {
				return null;
			}
		}

		public TestTLCDebugger() {
			launcher = new TestLauncher();
		}
	}
}
