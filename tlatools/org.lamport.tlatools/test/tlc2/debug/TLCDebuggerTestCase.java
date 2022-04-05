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
import static org.junit.Assert.assertNull;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.net.URI;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.Phaser;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.eclipse.lsp4j.debug.Breakpoint;
import org.eclipse.lsp4j.debug.ContinueArguments;
import org.eclipse.lsp4j.debug.EvaluateArguments;
import org.eclipse.lsp4j.debug.EvaluateArgumentsContext;
import org.eclipse.lsp4j.debug.EvaluateResponse;
import org.eclipse.lsp4j.debug.NextArguments;
import org.eclipse.lsp4j.debug.ReverseContinueArguments;
import org.eclipse.lsp4j.debug.Scope;
import org.eclipse.lsp4j.debug.SetBreakpointsArguments;
import org.eclipse.lsp4j.debug.Source;
import org.eclipse.lsp4j.debug.SourceBreakpoint;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.StackTraceArguments;
import org.eclipse.lsp4j.debug.StepInArguments;
import org.eclipse.lsp4j.debug.StepOutArguments;
import org.eclipse.lsp4j.debug.StoppedEventArguments;
import org.eclipse.lsp4j.debug.Variable;
import org.eclipse.lsp4j.debug.services.IDebugProtocolClient;
import org.eclipse.lsp4j.jsonrpc.Launcher;
import org.eclipse.lsp4j.jsonrpc.RemoteEndpoint;
import org.junit.Before;

import tla2sany.semantic.OpDeclNode;
import tlc2.debug.TLCStateStackFrame.DebuggerValue;
import tlc2.tool.TLCState;
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.util.Context;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;

public abstract class TLCDebuggerTestCase extends ModelCheckerTestCase implements IDebugProtocolClient {

	protected final TestTLCDebugger debugger = new TestTLCDebugger();
	protected final Phaser phase = new Phaser();

	public TLCDebuggerTestCase(String spec, String path, String[] extraArgs, final int exitStatus) {
		super(spec, path, Stream.of(extraArgs, new String[] { "-debugger", "-noGenerateSpecTE" }).flatMap(Stream::of).toArray(String[]::new),
				exitStatus);
		// (i) This/current/control/test thread and (ii) executor thread that runs TLC
		// and is launched in setUp below.
		phase.bulkRegister(2);

		// Register debugger and add a breakpoint *before* TLC gets started in setUp.
		TLCDebugger.Factory.OVERRIDE = debugger;
	}

	public TLCDebuggerTestCase(String spec, String path, final int exitStatus) {
		this(spec, path, new String[] {}, exitStatus);
	}
	
	@Override
	protected boolean runWithDebugger() {
		// TLCDebuggerTestCase configures the debugger explicitly! Especially, it
		// doesn't pass 'nosuspend,nohalt'.
		return false;
	}

	@Override
	protected boolean doDump() {
		return !super.doDump();
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

	protected OpDeclNode[] getVars() {
		// The order of vars is expected to be deterministic across tests!,
		return TLCState.Empty.getVars();
		// If this ever causes problems because Empty is still null during startup, an
		// alternative is:
		//		final Tool tool = (Tool) TLCGlobals.mainChecker.tool;
		//		return tool.getSpecProcessor().getVariablesNodes();
	}
	
	protected static SetBreakpointsArguments createBreakpointArgument(final String spec, final int line, final int column, final int hitCnt) {
		final SetBreakpointsArguments arguments = new SetBreakpointsArguments();
		final SourceBreakpoint breakpoint = new SourceBreakpoint();
		breakpoint.setLine(line);
		breakpoint.setColumn(column);
		if (hitCnt > -1) {
			breakpoint.setHitCondition(Integer.toString(hitCnt));
		}
		final SourceBreakpoint[] breakpoints = new SourceBreakpoint[] { breakpoint };
		arguments.setBreakpoints(breakpoints);
		final Source source = new Source();
		source.setName(spec);
		arguments.setSource(source);
		return arguments;
	}
	
	protected static SetBreakpointsArguments createBreakpointArgument(final String spec, final int line) {
		return createBreakpointArgument(spec, line, 0, -1);
	}

	protected static TLCActionStackFrame assertTLCActionFrame(final StackFrame stackFrame, final int beginLine, final int beginColumn,
			final int endLine, final int endColumn, String spec, final Context ctxt, final OpDeclNode... unassigned) {
		assertTLCActionFrame(stackFrame, beginLine, endLine, spec, ctxt, unassigned);
		assertEquals(beginColumn, stackFrame.getColumn());
		assertEquals(endColumn + 1, (int) stackFrame.getEndColumn());
		return (TLCActionStackFrame) stackFrame;
	}

	protected static void assertTLCActionFrame(final StackFrame stackFrame, final int beginLine, final int beginColumn,
			final int endLine, final int endColumn, String spec, final OpDeclNode... unassigned) {
		assertTLCActionFrame(stackFrame, beginLine, endLine, spec, Context.Empty, unassigned);
		assertEquals(beginColumn, stackFrame.getColumn());
		assertEquals(endColumn + 1, (int) stackFrame.getEndColumn());
	}

	protected static void assertTLCActionFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec, final OpDeclNode... unassigned) {
		assertTLCActionFrame(stackFrame, beginLine, endLine, spec, Context.Empty, unassigned);
	}

	protected static void assertTLCActionFrame(final StackFrame stackFrame, final int beginLine, final int beginColumn,
			final int endLine, final int endColumn, String spec, final Set<Variable> expected,
			final OpDeclNode... unassigned) {
		assertTLCActionFrame(stackFrame, beginLine, endLine, spec, expected, unassigned);
		assertEquals(beginColumn, stackFrame.getColumn());
		assertEquals(endColumn + 1, (int) stackFrame.getEndColumn());
	}

	protected static void assertTLCActionFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec, final Set<Variable> expected, final OpDeclNode... unassigned) {
		assertTLCFrame0(stackFrame, beginLine, endLine, spec, null);
		assertTrue(stackFrame instanceof TLCActionStackFrame);
		final TLCActionStackFrame f = (TLCActionStackFrame) stackFrame;
		// Showing variables in the debugger does *not* unlazy LazyValues, i.e.
		// interferes with TLC's evaluation.
		final List<LazyValue> lazies = new ArrayList<>();
		Context context = f.getContext();
		while (context != null) {
			if (context.getValue() instanceof LazyValue) {
				LazyValue lv = (LazyValue) context.getValue();
				if (lv.getValue() == null) {
					lazies.add(lv);
				}
			}
			context = context.next();
		}
		
		final List<Variable> variables = Arrays.asList(f.getVariables());
		assertEquals(f.getContext().toMap().size(), variables.size());
		NXT: for (Variable v : variables) {
			for (Variable e : expected) {
				if (e.getName().equals(v.getName()) && e.getValue().equals(v.getValue())
						&& e.getType().equals(v.getType())) {
					continue NXT;
				}
			}
			fail();
		}
		lazies.forEach(lv -> assertNull(lv.getValue()));
	}

	protected static void assertTLCActionFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec, final Context expectedContext, final OpDeclNode... unassigned) {
		assertTLCFrame0(stackFrame, beginLine, endLine, spec, expectedContext);

		assertTrue(stackFrame instanceof TLCActionStackFrame);
		final TLCActionStackFrame f = (TLCActionStackFrame) stackFrame;

		assertTrue(Arrays.asList(f.getScopes()).stream().filter(s -> TLCActionStackFrame.SCOPE.equals(s.getName()))
				.findAny().isPresent());

		assertNotNull(f.getS());
		assertTrue(f.getS().allAssigned());

		if (expectedContext != null && expectedContext.isEmpty()) {
			assertTrue(f.nestedVariables.isEmpty());
		}

		assertNotNull(f.state);
		assertEquals(new HashSet<>(Arrays.asList(unassigned)), f.state.getUnassigned());
		
		// Assert successor has an action set. This cannot be asserted for f.state
		// because f.state might have been read from its persisted state
		// (DiskStateQueue) that doesn't include f.state's action.
		assertNotNull(f.state.getAction());

		// Assert successor has a predecessor.
		assertNotNull(f.state.getPredecessor());

		assertStateVars(f, f.getS(), f.state);

		// Assert successor has a trace leading to an initial state.
		assertTrace(f, f.state);
		
		// Assert level of state and successor.
		if (!isStuttering(f.getS(), f.getT())) {
			assertEquals(f.getS().getLevel() + 1, f.state.getLevel());
		} else {
			// TLA+ allows stuttering to occur.  By definition, stuttering steps do *not* increase the level,
			// which is why tasf.successor has the same level of its predecessor.  If stuttering would be
			// taken into account by TLCGet("level"), each state s1 to s6 above could have any level except
			// level 1.  s1 would be the only state whose level would be 1 to inf. 
			assertEquals(f.getS().getLevel(), f.state.getLevel());
		}
	}

	private static boolean isStuttering(TLCState s, TLCState t) {
		// Iff s and t have all variables assigned, i.e., are fully evaluated, best we
		// can do is to compare all variable values.
		if (s.allAssigned() && t.allAssigned()) {
			// Evaluating equals, when not all variables are assigned, would cause a
			// NullPointerException in Value#equals.
			return s.getVals().equals(t.getVals());
		}
		return false;
	}

	protected static void assertTLCStateFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec, Map<String, String> expected) {
		assertTLCFrame0(stackFrame, beginLine, endLine, spec, null);

		assertTrue(stackFrame instanceof TLCStateStackFrame);
		assertFalse(stackFrame instanceof TLCActionStackFrame);
		final TLCStackFrame f = (TLCStackFrame) stackFrame;
		
		// Showing variables in the debugger does *not* unlazy LazyValues, i.e.
		// interferes with TLC's evaluation.
		final List<LazyValue> lazies = new ArrayList<>();
		Context context = f.getContext();
		while (context != null) {
			if (context.getValue() instanceof LazyValue) {
				LazyValue lv = (LazyValue) context.getValue();
				if (lv.getValue() == null) {
					lazies.add(lv);
				}
			}
			context = context.next();
		}
		
		final Variable[] variables = f.getVariables();
		assertEquals(expected.size(), variables.length);
		for (Variable variable : variables) {
			assertEquals(expected.get(variable.getName()), variable.getValue());
		}
		
		lazies.forEach(lv -> assertNull(lv.getValue()));
	}

	protected static void assertTLCStateFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec) {
		assertTLCStateFrame(stackFrame, beginLine, endLine, spec, new OpDeclNode[0]);
	}

	protected static void assertTLCStateFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec, final OpDeclNode... unassigned) {
		assertTLCStateFrame(stackFrame, beginLine, endLine, spec, Context.Empty, unassigned);
	}

	protected static void assertTLCStateFrame(final StackFrame stackFrame, final int beginLine, final int beginColumn,
			final int endLine, final int endColumn, String spec, final Context expectedContext,
			final OpDeclNode... unassigned) {
		assertTLCStateFrame(stackFrame, beginLine, endLine, spec, expectedContext, unassigned);
		assertEquals(beginColumn, stackFrame.getColumn());
		assertEquals(endColumn + 1, (int) stackFrame.getEndColumn());
	}

	protected static void assertTLCStateFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec, final Context expectedContext, final OpDeclNode... unassigned) {
		assertTLCFrame0(stackFrame, beginLine, endLine, spec, expectedContext);

		assertTrue(stackFrame instanceof TLCStateStackFrame);
		assertFalse(stackFrame instanceof TLCActionStackFrame);
		final TLCStateStackFrame f = (TLCStateStackFrame) stackFrame;

		if (expectedContext != null) {
			assertEquals(0, new ContextComparator().compare(expectedContext, f.getContext()));
		}

		if (expectedContext != null && expectedContext.isEmpty()) {
			assertTrue(f.nestedVariables.isEmpty());
		}

		assertNotNull(f.state);

		assertEquals(new HashSet<>(Arrays.asList(unassigned)), f.state.getUnassigned());
		
		assertStateVars(f, f.state);
		assertTrace(f, f.state);
	}

	private static void assertTrace(final TLCStateStackFrame frame, final TLCState st) {
		final Map<Integer, DebugTLCVariable> old = new HashMap<>(frame.nestedVariables);
		try {
			final List<DebugTLCVariable> trace = Arrays.asList(frame.getTrace()).stream()
					.map(v -> (DebugTLCVariable) v).collect(Collectors.toList());
			
			// Assert that the trace is never empty.
			assertTrue(trace.size() > 0);
						
			// Assert that the last state is an initial state.
			assertTrue(trace.get(trace.size() - 1).getName().startsWith("1: "));
			
			// Reverse the trace to traverse from initial to end in the following loops
			Collections.reverse(trace);
			
			// Assert that the variables' numbers in trace are strictly monotonic.
			for (int i = 0; i < trace.size(); i++) {
				assertTrue(trace.get(i).getName().startsWith(Integer.toString(i + 1) + ":"));
			}

			// Assert TLCState#allAssigned for all but the last state.
			for (int i = 0; i < trace.size() - 1; i++) {
				final Value tlcValue = trace.get(i).getTLCValue();
				assertTrue(tlcValue instanceof RecordValue);
				final RecordValue rv = (RecordValue) tlcValue;
				for (Value val : rv.values) {
					assertTrue(!(val instanceof StringValue) || !DebuggerValue.NOT_EVALUATED.equals(((StringValue) val).toString()));
				}
			}
		} finally {
			// TLCStateStackFrame#getTrace has the side-effect of adding variables to the
			// nested ones.
			frame.nestedVariables.clear();
			frame.nestedVariables.putAll(old);
		}
	}

	protected static void assertTLCSuccessorFrame(final StackFrame stackFrame, final int beginLine, final int beginColumn,
			final int endLine, final int endColumn, String spec, final Context expectedContext,
			final int expectedSuccessors, final OpDeclNode... unassigned) {
		assertTLCStateFrame(stackFrame, beginLine, endLine, spec, expectedContext, unassigned);
		assertEquals(beginColumn, stackFrame.getColumn());
		assertEquals(endColumn + 1, (int) stackFrame.getEndColumn());

		assertTrue(stackFrame instanceof TLCSuccessorsStackFrame);
		final TLCSuccessorsStackFrame succframe = (TLCSuccessorsStackFrame) stackFrame;

		if (!succframe.getSuccessors().isEmpty()) {
			final Scope succs = Arrays.asList(succframe.getScopes()).stream().filter(s -> s.getName().equals("Successors"))
					.reduce((a, b) -> a).get();
			assertNotNull(succs);
			
			List<Variable> variables = Arrays.asList(succframe.getVariables(succs.getVariablesReference()));
			assertEquals(expectedSuccessors, variables.size());
			
			final List<Value> stateRecords = variables.stream().map(v -> (DebugTLCVariable) v).map(d -> d.getTLCValue())
					.collect(Collectors.toList());
			final Set<RecordValue> successors = succframe.getSuccessors().stream().map(s -> new RecordValue(s))
					.collect(Collectors.toSet());
			for (Value s : stateRecords) {
				assertTrue(successors.contains(s));
			}
		} else {
			Optional<Scope> o = Arrays.asList(succframe.getScopes()).stream().filter(s -> s.getName().equals("Successors"))
					.reduce((a, b) -> a);
			assertTrue(o.isEmpty());
		}
	}
	
	private static void assertStateVars(TLCStateStackFrame frame, final TLCState st) {
		final Map<Integer, DebugTLCVariable> old = new HashMap<>(frame.nestedVariables);
		try {
			final Variable[] svs = frame.getStateVariables();
			assertEquals(1, svs.length);
			assertTrue(svs[0] instanceof DebugTLCVariable);
			assertEquals(st.allAssigned() ? new RecordValue(st) : new RecordValue(st, TLCStateStackFrame.NOT_EVAL),
					((DebugTLCVariable) svs[0]).getTLCValue());
		} finally {
			// TLCStateStackFrame#getStateVariables has the side-effect of adding variables to the
			// nested ones.
			frame.nestedVariables.clear();
			frame.nestedVariables.putAll(old);
		}
	}
	
	private static void assertStateVars(TLCActionStackFrame frame, final TLCState s, final TLCState t) {
		final Map<Integer, DebugTLCVariable> old = new HashMap<>(frame.nestedVariables);
		try {
			final Variable[] svs = frame.getStateVariables();
			assertEquals(1, svs.length);
			assertTrue(svs[0] instanceof DebugTLCVariable);
			assertEquals(t.allAssigned() ? new RecordValue(s, t, new StringValue("Should not be used")) : new RecordValue(s, t, TLCStateStackFrame.NOT_EVAL),
					((DebugTLCVariable) svs[0]).getTLCValue());
		} finally {
			// TLCStateStackFrame#getStateVariables has the side-effect of adding variables to the
			// nested ones.
			frame.nestedVariables.clear();
			frame.nestedVariables.putAll(old);
		}
	}

	protected static void assertTLCFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec) {
		assertTLCFrame(stackFrame, beginLine, endLine, spec, Context.Empty);
	}
	
	protected static void assertTLCFrame(final StackFrame stackFrame, final int beginLine, final int beginColumn,
			final int endLine, final int endColumn, String spec) {
		assertTLCFrame(stackFrame, beginLine, endLine, spec);
		assertEquals(beginColumn, stackFrame.getColumn());
		assertEquals(endColumn + 1, (int) stackFrame.getEndColumn());
	}
	
	protected static void assertTLCFrame(final StackFrame stackFrame, final int beginLine, final int beginColumn,
			final int endLine, final int endColumn, String spec, final Context expectedContext) {
		assertTLCFrame(stackFrame, beginLine, endLine, spec, expectedContext);
		assertEquals(beginColumn, stackFrame.getColumn());
		assertEquals(endColumn + 1, (int) stackFrame.getEndColumn());
	}

	protected static void assertTLCFrame(final StackFrame stackFrame, final int beginLine, final int endLine,
			String spec, final Context expectedContext) {
		assertTLCFrame0(stackFrame, beginLine, endLine, spec, expectedContext);
		assertFalse(stackFrame instanceof TLCStateStackFrame);
		assertFalse(stackFrame instanceof TLCActionStackFrame);
	}

	private static void assertTLCFrame0(final StackFrame stackFrame, final int beginLine, final int endLine,
				String spec, final Context expectedContext) {
		assertNotNull(stackFrame);
		assertEquals(beginLine, stackFrame.getLine());
		assertEquals(endLine, (int) stackFrame.getEndLine());
		assertEquals(spec, stackFrame.getSource().getName());
		assertTrue(stackFrame instanceof TLCStackFrame);
		final TLCStackFrame f = (TLCStackFrame) stackFrame;
		assertNotNull(f.getTool());


		final Optional<Scope> scope = Arrays.asList(f.getScopes()).stream()
				.filter(s -> TLCStackFrame.SCOPE.equals(s.getName())).findAny();
		if (expectedContext != null && expectedContext == Context.Empty) {
			assertFalse(scope.isPresent());
			return;
		}
		assertTrue(scope.isPresent());
		
		Scope sp = scope.get();
		Variable[] variables = f.getVariables(sp.getVariablesReference());
		assertNotNull(variables);
		if (expectedContext!=null) {
			assertEquals(0, new ContextComparator().compare(expectedContext, f.getContext()));
			assertEquals(f.getContext().toMap().size(), variables.length);
		}
	}

	protected static Variable createVariable(String name, String value, String type) {
		Variable e = new Variable();
		e.setName(name);
		e.setValue(value);
		e.setType(type);
		return e;
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

		public Breakpoint[] replaceAllBreakpointsWithUnchecked(final String rootModule, int line) {
			unsetBreakpoints();
			// Set new breakpoint.
			try {
				return setBreakpoints(rootModule, line);
			} catch (Exception e) {
				return new Breakpoint[0];
			}
		}

		/**
		 * Replaces all existing breakpoints in all modules with the given one. Compared
		 * to TLCDebugger.setBreakpoints(..), this does replace breakpoints even in
		 * other modules.
		 */
		public Breakpoint[] replaceAllBreakpointsWith(final String rootModule, int line) throws Exception {
			unsetBreakpoints();
			// Set new breakpoint.
			return setBreakpoints(rootModule, line);
		}
		
		public Breakpoint[] setBreakpoints(final String rootModule, int line) throws Exception {
			return setBreakpoints(createBreakpointArgument(rootModule, line)).get().getBreakpoints();
		}

		public void unsetBreakpoints() {
			new HashSet<>(breakpoints.keySet()).forEach(module -> {
				final SetBreakpointsArguments args = new SetBreakpointsArguments();
				args.setBreakpoints(new SourceBreakpoint[0]);
				final Source source = new Source();
				source.setName(module);
				args.setSource(source);
				setBreakpoints(args);
			});
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
		
		public StackFrame[] next(final int steps) throws Exception {
			// Convenience methods
			for (int i = 0; i < steps; i++) {
				next(new NextArguments()).whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
			}
			return stackTrace();
		}

		public StackFrame[] stepOut(final int steps) throws Exception {
			for (int i = 0; i < steps; i++) {
				stepOut(new StepOutArguments()).whenComplete((a, b) -> phase.arriveAndAwaitAdvance());			}
			return stackTrace();
		}
		
		public StackFrame[] stepOut() throws Exception {
			// Convenience methods
			stepOut(new StepOutArguments()).whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
			return stackTrace();
		}

		public StackFrame[] stepIn(final int steps) throws Exception {
			// Convenience methods
			for (int i = 0; i < steps; i++) {
				stepIn(new StepInArguments()).whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
			}
			return stackTrace();
		}

		public StackFrame[] stepIn() throws Exception {
			return stepIn(1);
		}

		public StackFrame[] continue_() throws Exception {
			// Convenience methods
			continue_(new ContinueArguments()).whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
			return stackTrace();
		}

		public StackFrame[] reverseContinue() throws Exception {
			// Convenience methods
			reverseContinue(new ReverseContinueArguments()).whenComplete((a, b) -> phase.arriveAndAwaitAdvance());
			return stackTrace();
		}

		public EvaluateResponse evaluate(final String module, final String symbol, final int beginLine,
				final int beginColumn, final int endLine, final int endColumn) throws Exception {
			final EvaluateArguments args = new EvaluateArguments();
			args.setContext(EvaluateArgumentsContext.HOVER);
			// Resolve module to absolute path required by URI.
			final URI uri = new URI("tlaplus", "", Paths.get(module).toAbsolutePath().toString(), symbol,
					String.format("%s %s %s %s", beginLine, beginColumn, endLine, endColumn));
			args.setExpression(uri.toASCIIString());
			args.setFrameId(this.stack.peek().getId()); // Just use the id of the topmost frame.
			return evaluate(args).get();
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
