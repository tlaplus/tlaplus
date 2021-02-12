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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Stack;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.Executors;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.eclipse.lsp4j.debug.Breakpoint;
import org.eclipse.lsp4j.debug.BreakpointLocation;
import org.eclipse.lsp4j.debug.BreakpointLocationsArguments;
import org.eclipse.lsp4j.debug.BreakpointLocationsResponse;
import org.eclipse.lsp4j.debug.CancelArguments;
import org.eclipse.lsp4j.debug.Capabilities;
import org.eclipse.lsp4j.debug.ConfigurationDoneArguments;
import org.eclipse.lsp4j.debug.ContinueArguments;
import org.eclipse.lsp4j.debug.ContinueResponse;
import org.eclipse.lsp4j.debug.DisconnectArguments;
import org.eclipse.lsp4j.debug.EvaluateArguments;
import org.eclipse.lsp4j.debug.EvaluateResponse;
import org.eclipse.lsp4j.debug.InitializeRequestArguments;
import org.eclipse.lsp4j.debug.NextArguments;
import org.eclipse.lsp4j.debug.OutputEventArguments;
import org.eclipse.lsp4j.debug.PauseArguments;
import org.eclipse.lsp4j.debug.ScopesArguments;
import org.eclipse.lsp4j.debug.ScopesResponse;
import org.eclipse.lsp4j.debug.SetBreakpointsArguments;
import org.eclipse.lsp4j.debug.SetBreakpointsResponse;
import org.eclipse.lsp4j.debug.SetVariableArguments;
import org.eclipse.lsp4j.debug.SetVariableResponse;
import org.eclipse.lsp4j.debug.Source;
import org.eclipse.lsp4j.debug.SourceBreakpoint;
import org.eclipse.lsp4j.debug.StackFrame;
import org.eclipse.lsp4j.debug.StackTraceArguments;
import org.eclipse.lsp4j.debug.StackTraceResponse;
import org.eclipse.lsp4j.debug.StepInArguments;
import org.eclipse.lsp4j.debug.StepOutArguments;
import org.eclipse.lsp4j.debug.StoppedEventArguments;
import org.eclipse.lsp4j.debug.Thread;
import org.eclipse.lsp4j.debug.ThreadsResponse;
import org.eclipse.lsp4j.debug.Variable;
import org.eclipse.lsp4j.debug.VariablesArguments;
import org.eclipse.lsp4j.debug.VariablesResponse;
import org.eclipse.lsp4j.debug.services.IDebugProtocolClient;
import org.eclipse.lsp4j.jsonrpc.Launcher;

import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;

public abstract class TLCDebugger extends AbstractDebugger implements IDebugTarget {
	protected static Logger LOGGER = Logger.getLogger(TLCDebugger.class.getName());

	protected Launcher<IDebugProtocolClient> launcher;

	@Override
	public synchronized CompletableFuture<Capabilities> initialize(InitializeRequestArguments args) {
		LOGGER.finer("initialize");

		Executors.newSingleThreadExecutor().submit(() -> {
			LOGGER.finer("initialize -> initialized");
			// Signal the debugger that we are ready. It seem not relevant in what order the
			// response below and the initialized signal arrive at the debugger.
			launcher.getRemoteProxy().initialized();
		});

		// The capabilities define customizations how the debugger will interact with
		// this debuggee. Declaring no capabilities causes the most simple protocol to
		// be used.
		final Capabilities capabilities = new Capabilities();
		capabilities.setSupportsEvaluateForHovers(true);
		return CompletableFuture.completedFuture(capabilities);
	}

	@Override
	public CompletableFuture<EvaluateResponse> evaluate(final EvaluateArguments args) {
		// See https://github.com/alygin/vscode-tlaplus/blob/master/src/main.ts
		if (args.getExpression().startsWith("tlaplus://")) {
			return CompletableFuture.completedFuture(this.stack.stream().filter(f -> f.getId() == args.getFrameId())
					.findAny().map(f -> f.get(args)).orElse(new EvaluateResponse()));
		}
		return CompletableFuture.completedFuture(new EvaluateResponse());
	}

	@Override
	public synchronized CompletableFuture<Void> cancel(CancelArguments args) {
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public synchronized CompletableFuture<Void> configurationDone(ConfigurationDoneArguments args) {
		LOGGER.finer("configurationDone");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public synchronized CompletableFuture<BreakpointLocationsResponse> breakpointLocations(BreakpointLocationsArguments args) {
		LOGGER.finer("breakpointLocations");
		final BreakpointLocationsResponse response = new BreakpointLocationsResponse();
		BreakpointLocation breakpoint = new BreakpointLocation();
		breakpoint.setColumn(args.getColumn());
		breakpoint.setEndColumn(args.getEndColumn());
		breakpoint.setEndLine(args.getEndLine());
		breakpoint.setLine(args.getLine());
		BreakpointLocation[] breakpoints = new BreakpointLocation[] { breakpoint };
		response.setBreakpoints(breakpoints);
		return CompletableFuture.completedFuture(response);
	}

	private final List<Breakpoint> breakpoints = Collections.synchronizedList(new ArrayList<>());

	@Override
	public synchronized CompletableFuture<Void> disconnect(DisconnectArguments args) {
		LOGGER.finer("disconnect");
		
		breakpoints.clear();
		targetLevel = -1;
		step = Step.Continue;
		this.notify();
		
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public synchronized CompletableFuture<SetBreakpointsResponse> setBreakpoints(SetBreakpointsArguments args) {
		//TODO: Confirm breakpoint locations (see tlc2.debug.TLCDebugger.matches(SemanticNode))!!!
		LOGGER.finer("setBreakpoints");
		final SourceBreakpoint[] sbps = args.getBreakpoints();
		
		final ArrayList<Breakpoint> tmp = new ArrayList<>(sbps.length);
		for (int j = 0; j < sbps.length; j++) {
			Breakpoint breakpoint = new Breakpoint();
			breakpoint.setColumn(sbps[j].getColumn());
			breakpoint.setLine(sbps[j].getLine());
			breakpoint.setId(j);
			breakpoint.setVerified(true);
			Source source = args.getSource();
			breakpoint.setSource(source);
			tmp.add(breakpoint);
		}
		breakpoints.clear();
		breakpoints.addAll(tmp);
		
		final SetBreakpointsResponse response = new SetBreakpointsResponse();
		response.setBreakpoints(breakpoints.toArray(new Breakpoint[breakpoints.size()]));
		return CompletableFuture.completedFuture(response);
	}

	@Override
	public synchronized CompletableFuture<StackTraceResponse> stackTrace(StackTraceArguments args) {
		LOGGER.finer(String.format("stackTrace frame: %s, levels: %s\n", args.getStartFrame(), args.getLevels()));
		final StackTraceResponse res = new StackTraceResponse();

		int from = stack.size() - 1;
		if (args.getStartFrame() != null) {
			int req = args.getStartFrame();
			// within bounds.
			if (req < 0 || stack.size() - 1 < req) {
				res.setStackFrames(new StackFrame[0]);
				return CompletableFuture.completedFuture(res);
			}
			from = from - req;
		}

		int to = 0;
		if (args.getLevels() != null) {
			int req = args.getLevels();
			// If not within bounds, ignore levels.
			if (req != 0 && req < from) {
				to = from - (req - 1);
			}
		}
		
		final List<StackFrame> frames = new ArrayList<>(Math.max(from - to, 0));
		for (; from >= to; from--) {
			final TLCStackFrame stackFrame = stack.elementAt(from);
			frames.add(stackFrame);
		}

		res.setStackFrames(frames.toArray(new StackFrame[frames.size()]));
		res.setTotalFrames(stack.size());
		return CompletableFuture.completedFuture(res);
	}

	@Override
	public synchronized CompletableFuture<ScopesResponse> scopes(ScopesArguments args) {
		LOGGER.finer(String.format("scopes frame %s\n", args.getFrameId()));

		final ScopesResponse response = new ScopesResponse();

		stack.stream().filter(s -> s.getId() == args.getFrameId()).findFirst()
				.ifPresent(frame -> response.setScopes(frame.getScopes()));

		return CompletableFuture.completedFuture(response);
	}

	@Override
	public synchronized CompletableFuture<VariablesResponse> variables(VariablesArguments args) {
		final int vr = args.getVariablesReference();

		final VariablesResponse value = new VariablesResponse();
		
		final List<Variable> collect = new ArrayList<>(); 
		for (TLCStackFrame frame : this.stack) {
			collect.addAll(Arrays.asList(frame.getVariables(vr)));
		}
		value.setVariables(collect.toArray(new Variable[collect.size()]));
		
		return CompletableFuture.completedFuture(value);
	}

	@Override
	public synchronized CompletableFuture<SetVariableResponse> setVariable(SetVariableArguments args) {
		LOGGER.finer("setVariable");
		return CompletableFuture.completedFuture(new SetVariableResponse());
	}

	@Override
	public synchronized CompletableFuture<ThreadsResponse> threads() {
		LOGGER.finer("threads");
		Thread thread = new Thread();
		thread.setId(0);
		thread.setName("worker");
		ThreadsResponse res = new ThreadsResponse();
		res.setThreads(new Thread[] { thread });
		return CompletableFuture.completedFuture(res);
	}

	@Override
	public synchronized CompletableFuture<ContinueResponse> continue_(ContinueArguments args) {
		LOGGER.finer("continue_");
		targetLevel = -1;
		step = Step.Continue;
		this.notify();
		return CompletableFuture.completedFuture(new ContinueResponse());
	}

	@Override
	public synchronized CompletableFuture<Void> next(NextArguments args) {
		LOGGER.finer("next/stepOver");
		targetLevel = this.stack.size();
		step = Step.Over;
		this.notify();
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public synchronized CompletableFuture<Void> stepIn(StepInArguments args) {
		LOGGER.finer("stepIn");
		// matches(..) below does not take targetLevel into account, thus not changing
		// it here. The reason is that it is surprising if step.in on a leaf-frame
		// would amount to resume/continue.
		step = Step.In;
		this.notify();
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public synchronized CompletableFuture<Void> stepOut(StepOutArguments args) {
		LOGGER.finer("stepOut");
		targetLevel = this.stack.size();
		step = Step.Out;
		this.notify();
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public synchronized CompletableFuture<Void> pause(PauseArguments args) {
		LOGGER.finer("pause");
		Executors.newSingleThreadExecutor().submit(() -> {
			LOGGER.finer("pause -> stopped");
			StoppedEventArguments eventArguments = new StoppedEventArguments();
			eventArguments.setThreadId(0);
			eventArguments.setReason("pause");
			launcher.getRemoteProxy().stopped(eventArguments);
		});
		return CompletableFuture.completedFuture(null);
	}

	// 8888888888888888888888888888888888888888888888888888888888888888888888888 //

	//TODO: Instead of maintaining the stack here, we could evaluated with CallStackTool
	// that will get the job done for us (tlc2.tool.impl.CallStackTool.callStack).
	// However, CST only keeps the SemanticNode but skips the Context and the values. We
	// would have to make CST take a function that applies a transformation for the debugger
	// and a different one when CST does its original job.
	protected final Stack<TLCStackFrame> stack = new Stack<>();
	
	// Initialize the debugger to immediately halt on the first frame.
	private volatile int targetLevel = 1;
	private volatile Step step = Step.In;

	@Override
	public synchronized IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c, int control) {
		stack.push(new TLCStackFrame(expr, c, tool));
		haltExecution(expr, this.stack.size());
		return this;
	}

	@Override
	public synchronized IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c, TLCState ps) {
		stack.push(new TLCStateStackFrame(expr, c, tool, ps));
		haltExecution(expr, this.stack.size());
		return this;
	}

	@Override
	public synchronized IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c, TLCState predecessor,
			TLCState ps) {
		stack.push(new TLCActionStackFrame(expr, c, tool, predecessor, ps));
		haltExecution(expr, this.stack.size());
		return this;
	}

	@Override
	public synchronized IDebugTarget pushFrame(TLCState state) {
		TLCStackFrame f = this.stack.peek();
		pushFrame(f.getTool(), f.getNode(), f.getContext(), state);
		return this;
	}

	@Override
	public synchronized IDebugTarget pushFrame(TLCState predecessor, TLCState state) {
		TLCStackFrame f = this.stack.peek();
		return pushFrame(f.getTool(), f.getNode(), f.getContext(), predecessor, state);
	}

	@Override
	public synchronized IDebugTarget popFrame(TLCState state) {
		TLCStackFrame f = this.stack.peek();
		return popFrame(f.getTool(), f.getNode(), f.getContext(), state);
	}

	@Override
	public synchronized IDebugTarget popFrame(TLCState predecessor, TLCState state) {
		//TODO This swallows the predecessor!
		return popFrame(state);
	}

	@Override
	public synchronized IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, int control) {
		if (LOGGER.isLoggable(Level.FINER)) {
			LOGGER.finer(String.format("%s Call popFrame: [%s], level: %s\n",
					new String(new char[this.stack.size()]).replace('\0', '#'), expr, this.stack.size()));
		}
		final TLCStackFrame pop = stack.pop();
		assert expr == pop.getNode();
		return this;
	}

	@Override
	public synchronized IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, TLCState ps) {
		final TLCStackFrame pop = stack.pop();
		assert expr == pop.getNode();
		return this;
	}

	@Override
	public synchronized IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, TLCState predecessor, TLCState ps) {
		return popFrame(tool, expr, c, ps);
	}

	@Override
	public synchronized IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c, RuntimeException e) {
		return pushExceptionFrame(new TLCStackFrame(expr, c, tool, e), e);
	}
	
	@Override
	public synchronized IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c,
			TLCState state, RuntimeException e) {
		return pushExceptionFrame(new TLCStateStackFrame(expr, c, tool, state, e), e);
	}
	
	@Override
	public synchronized IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c, TLCState predecessor,
			TLCState state, RuntimeException e) {
		return pushExceptionFrame(new TLCActionStackFrame(expr, c, tool, predecessor, state, e), e);
	}

	private IDebugTarget pushExceptionFrame(final TLCStackFrame frame, RuntimeException e) {
		// Let the client print the exception in its debug output UI.
		final OutputEventArguments oea = new OutputEventArguments();
		oea.setOutput(e.getMessage());
		if (launcher != null) {
			launcher.getRemoteProxy().output(oea);
		}
		
		stack.push(frame);
		
		haltExecution();
		return this;
	}

	protected void haltExecution(final SemanticNode expr, final int level) {
		if (LOGGER.isLoggable(Level.FINER)) {
			LOGGER.finer(String.format("%s(%s): [%s]\n", new String(new char[level]).replace('\0', '#'), level, expr));
		}
		if (matches(step, targetLevel, level) || matches(expr)) {
			haltExecution();
		}
	}

	protected void haltExecution() {
		sendStopped();

		try {
			// Halt TLC's evaluation by blocking on this (one-element) queue. The DAP
			// front-end will add an element that will unblock us.
			this.wait();
		} catch (InterruptedException notExpectedToHappen) {
			notExpectedToHappen.printStackTrace();
			java.lang.Thread.currentThread().interrupt();
		}
	}

	protected void sendStopped() {
		LOGGER.finer("loadSource -> stopped");
		StoppedEventArguments eventArguments = new StoppedEventArguments();
		eventArguments.setThreadId(0);
		launcher.getRemoteProxy().stopped(eventArguments);
	}

	private static boolean matches(Step dir, int targetLevel, int currentLevel) {
		if (dir == Step.In) {
			// TODO With this conditional, step.in becomes continue when one steps into a
			// leave frame.  The debuggers that I know don't continue in this case.
//			if (currentLevel >= targetLevel) {
				return true;
//			}
		} else if (dir == Step.Over) {
			if (currentLevel == targetLevel) {
				return true;
			}
		} else if (dir == Step.Out) {
			// When stepping out, level has to be greater than or zero/0;
			if (currentLevel < targetLevel || currentLevel == 0) {
				return true;
			}
		}
		return false;
	}

	private boolean matches(final SemanticNode expr) {
		//TODO: Better match the location.  However, it shouldn't be done down here
		// but in setBreakpoints above that lets the debuggee tell the front-end
		// that a user-defined location is "corrected" to one that matches the bounds
		// of an expression in the semantic graph that is evaluated.  In other words,
		// setBreakpoints should traverse the semantic graph trying to find the smallest
		// i.e. best match for the given editor location.  The code here should then
		// simple compare the two location instances.
		final Location location = expr.getLocation();
		final String module = location.source();
		return breakpoints.stream().anyMatch(b -> {
			return b.getLine() == location.beginLine()
					// TODO: Stripping off the file suffix here is a hack, but is this even
					// necessary?
					&& module.equals(b.getSource().getName().replaceFirst(".tla$", ""));
		});
	}
	
	public static class Factory {

		public static TLCDebugger OVERRIDE;

		public static TLCDebugger getInstance() throws Exception {
			if (OVERRIDE != null) {
				return OVERRIDE;
			}
			return new AttachingDebugger();
		}
	}
}
