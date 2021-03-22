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
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.Executors;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.eclipse.lsp4j.debug.Breakpoint;
import org.eclipse.lsp4j.debug.Capabilities;
import org.eclipse.lsp4j.debug.ConfigurationDoneArguments;
import org.eclipse.lsp4j.debug.ContinueArguments;
import org.eclipse.lsp4j.debug.ContinueResponse;
import org.eclipse.lsp4j.debug.DisconnectArguments;
import org.eclipse.lsp4j.debug.EvaluateArguments;
import org.eclipse.lsp4j.debug.EvaluateArgumentsContext;
import org.eclipse.lsp4j.debug.EvaluateResponse;
import org.eclipse.lsp4j.debug.ExceptionBreakpointsFilter;
import org.eclipse.lsp4j.debug.InitializeRequestArguments;
import org.eclipse.lsp4j.debug.NextArguments;
import org.eclipse.lsp4j.debug.OutputEventArguments;
import org.eclipse.lsp4j.debug.PauseArguments;
import org.eclipse.lsp4j.debug.ScopesArguments;
import org.eclipse.lsp4j.debug.ScopesResponse;
import org.eclipse.lsp4j.debug.SetBreakpointsArguments;
import org.eclipse.lsp4j.debug.SetBreakpointsResponse;
import org.eclipse.lsp4j.debug.SetExceptionBreakpointsArguments;
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
import org.eclipse.lsp4j.debug.TerminateArguments;
import org.eclipse.lsp4j.debug.TerminatedEventArguments;
import org.eclipse.lsp4j.debug.Thread;
import org.eclipse.lsp4j.debug.ThreadsResponse;
import org.eclipse.lsp4j.debug.Variable;
import org.eclipse.lsp4j.debug.VariablesArguments;
import org.eclipse.lsp4j.debug.VariablesResponse;
import org.eclipse.lsp4j.debug.services.IDebugProtocolClient;
import org.eclipse.lsp4j.jsonrpc.Launcher;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tlc2.TLCGlobals;
import tlc2.tool.Action;
import tlc2.tool.TLCState;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.Value;

public abstract class TLCDebugger extends AbstractDebugger implements IDebugTarget {
	protected static Logger LOGGER = Logger.getLogger(TLCDebugger.class.getName());

	protected Launcher<IDebugProtocolClient> launcher;

	private Tool tool;

	public TLCDebugger() {
		this.step = Step.In;
		this.halt = true;
	}

	public TLCDebugger(final Step s, final boolean halt) {
		this.step = s;
		this.halt = halt;
	}
	
	public abstract TLCDebugger listen(int debugPort);

	@Override
	public IDebugTarget setTool(final Tool tool) {
		this.tool = tool;
		return this;
	}

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
		capabilities.setSupportsTerminateRequest(true);
		// Don't support ExceptionInfo requests. The previous git commit of the one that
		// introduces this message implements the request, and we learned that EI are
		// only useful if we wish to show the Java stack trace (which users don't care
		// about).
		capabilities.setSupportsExceptionInfoRequest(false);
		// Let users flip at runtime the value of "nohalt" that they passed as a
		// sub-command of the "-debugger" (see tlc2.TLC.java) command.
		capabilities.setExceptionBreakpointFilters(getExceptionBreakpointFilters());
		// Don't support more sophisticated configuration of exception breakpoint
		// filters such as ignoring some exceptions. When TLC hits an exception, it
		// terminates anyway.
		capabilities.setSupportsExceptionOptions(false);
		// Breakpoints:
		capabilities.setSupportsHitConditionalBreakpoints(true);
		// TODO: Log points and conditional (expression-based) breakpoints require to
		// parse TLA+ expressions after the spec has been parsed, which is not supported
		// by SANY.
		capabilities.setSupportsConditionalBreakpoints(false);
		capabilities.setSupportsLogPoints(false);
		return CompletableFuture.completedFuture(capabilities);
	}

	private ExceptionBreakpointsFilter[] getExceptionBreakpointFilters() {
		final ExceptionBreakpointsFilter filter = new ExceptionBreakpointsFilter();
		filter.setDefault_(this.halt);
		filter.setFilter("ExceptionBreakpointsFilter");
		filter.setLabel("Halt (break) on exceptions");
		return new ExceptionBreakpointsFilter[] {filter};
	}

	@Override
	public synchronized CompletableFuture<Void> setExceptionBreakpoints(SetExceptionBreakpointsArguments args) {
		if (Arrays.asList(args.getFilters()).contains("ExceptionBreakpointsFilter")) {
			this.halt = true;
		} else {
			this.halt = false;
		}
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public synchronized CompletableFuture<EvaluateResponse> evaluate(final EvaluateArguments args) {
		// See https://github.com/alygin/vscode-tlaplus/blob/master/src/main.ts
		if (EvaluateArgumentsContext.HOVER.equals(args.getContext()) && args.getExpression().startsWith("tlaplus://")) {
			return CompletableFuture.completedFuture(this.stack.stream().filter(f -> f.getId() == args.getFrameId())
					.findAny().map(f -> f.get(args)).orElse(new EvaluateResponse()));
		} else if (EvaluateArgumentsContext.REPL.equals(args.getContext())) {
			// TODO: Users can enter (arbitrary) expressions in the front-end's "Debug
			// Console". We could try to handle valid TLA+ expressions here, but SANY
			// unfortunately lacks incremental parsing.  Study related discussion started
			// in http://discuss.tlapl.us/msg01427.html and continued offline in the involved
			// inboxes.
		}
		return CompletableFuture.completedFuture(new EvaluateResponse());
	}
	
	// See setSupportsTerminateRequest above.
	@Override
	public synchronized CompletableFuture<Void> terminate(TerminateArguments args) {
		LOGGER.finer("terminate");
		// TODO: In case the debugger is currently paused on an ASSUME, TLC will first
		// generate the initial states before stopping.
		if (TLCGlobals.mainChecker != null) {
			TLCGlobals.mainChecker.stop();
		}
		if (TLCGlobals.simulator != null) {
			TLCGlobals.simulator.stop();
		}
		
		if (launcher != null) {
			// Notify the front-end that the debugger has terminated. Do this before notify
			// is called in disconnect to not create a race condition, i.e. failing to send
			// terminated because TLC quit.
			launcher.getRemoteProxy().terminated(new TerminatedEventArguments());
		}

		return disconnect(new DisconnectArguments());
	}
	
	@Override
	public synchronized CompletableFuture<Void> disconnect(DisconnectArguments args) {
		LOGGER.finer("disconnect");
		
		// "Unlock" evaluation, i.e. set step to Continue and clear all breakpoints.
		// Afterwards, resume TLC in case it's waiting for the debugger too.
		breakpoints.clear();
		targetLevel = -1;
		step = Step.Continue;
		halt = false;
		this.notify();
		
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public synchronized CompletableFuture<Void> configurationDone(ConfigurationDoneArguments args) {
		LOGGER.finer("configurationDone");
		return CompletableFuture.completedFuture(null);
	}

	protected final Map<String, List<TLCSourceBreakpoint>> breakpoints = new HashMap<>();

	@Override
	public synchronized CompletableFuture<SetBreakpointsResponse> setBreakpoints(final SetBreakpointsArguments args) {
		//TODO: Confirm breakpoint locations (see tlc2.debug.TLCDebugger.matches(SemanticNode))!!!
		LOGGER.finer("setBreakpoints");
		
		final String module = args.getSource().getName().replaceFirst(".tla$", "");
		
		if (args.getBreakpoints() != null && args.getBreakpoints().length > 0) {
			breakpoints.computeIfAbsent(module, key -> new ArrayList<TLCSourceBreakpoint>()).clear();
			
			final ModuleNode moduleNode = tool.getModule(module);
			
			final SourceBreakpoint[] sbps = args.getBreakpoints();
			final Breakpoint[] bp = new Breakpoint[sbps.length];
			for (int j = 0; j < sbps.length; j++) {
				final TLCSourceBreakpoint sbp = new TLCSourceBreakpoint(module, sbps[j]);
				breakpoints.get(module).add(sbp);
				
				// Create the response that communicates the result of setting the breakpoint.
				// We could try to verify the location of breakpoints.
				final Breakpoint breakpoint = new Breakpoint();
				breakpoint.setColumn(sbp.getColumn());
				breakpoint.setLine(sbp.getLine());
				breakpoint.setId(j);
				// Verify breakpoints. However, we only get the beginLine and
				// (optionally) beginColumn, but not endLine or endColumn, which
				// makes this fuzzy.  This doesn't matter though, as we
				// still create the breakpoint; only the user sees a visual cue.
				// I considered only to walk tool.getActions, tool.getInvariants,
				// getStateConstraints, getActionConstraionts, ..., but this causes
				// breakpoints in a high-level spec (refinement mapping) to
				// incorrectly show breakpoints as unverified.
				breakpoint.setVerified(
						// moduleNode is null if the front-end has a spec open (with breakpoints) that is
						// not part of the debugged spec and its modules.  For example, this might be a
						// module in the current folder that is neither extended nor instantiated.
						moduleNode == null || moduleNode.walkChildren(new SemanticNode.ChildrenVisitor<Boolean>() {
							private boolean verified = false;

							public void preVisit(final SemanticNode node) {
								final Location location = node.getLocation();
								// TODO: Include beginColumn/column here and where we handle breakpoints.
								if (location.beginLine() == sbp.getLine() && location.endLine() == sbp.getLine()) {
									this.verified = true;
								}
							}

							public boolean preempt(SemanticNode node) {
								return verified || !node.getLocation().includes(sbp.getLocation());
							}

							public Boolean get() {
								return verified;
							}
						}).get());
				// TODO: Set message why the breakpoint could not be set. E.g. would be useful
				// if a user tries to add a breakpoint at a temporal property such as the
				// behavior spec. The Next relation is another candidate when TLC decomposes it
				// into sub-actions s.t. a breakpoint on Next will never hit.
				
				final Source source = args.getSource();
				breakpoint.setSource(source);
				bp[j] = breakpoint;
			}
			final SetBreakpointsResponse response = new SetBreakpointsResponse();
			response.setBreakpoints(bp);
			return CompletableFuture.completedFuture(response);
		} else {
			breakpoints.getOrDefault(module, new ArrayList<>()).clear();
			return CompletableFuture.completedFuture(new SetBreakpointsResponse());
		}
	}

	@Override
	public synchronized CompletableFuture<StackTraceResponse> stackTrace(StackTraceArguments args) {
		LOGGER.finer(String.format("stackTrace frame: %s, levels: %s\n", args.getStartFrame(), args.getLevels()));
		final StackTraceResponse res = new StackTraceResponse();

		int from = 0;
		if (args.getStartFrame() != null) {
			int req = args.getStartFrame();
			// within bounds.
			if (req < 0 || stack.size() - 1 < req) {
				res.setStackFrames(new StackFrame[0]);
				return CompletableFuture.completedFuture(res);
			}
			from = req;
		}

		int to = stack.size(); // No decrement by one because subList is exclusive.
		if (args.getLevels() != null) {
			int req = args.getLevels();
			// If not within bounds, ignore levels.
			if (req > 0 && from + req < to) {
				to = from + req;
			}
		}
		
		final List<TLCStackFrame> frames = stack.subList(from, to);
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
	protected final LinkedList<TLCStackFrame> stack = new LinkedList<>();
	
	// Initialize the debugger to immediately halt on the first frame.
	private volatile int targetLevel = 1;
	private volatile Step step = Step.In;
	
	private volatile boolean halt;

	@Override
	public synchronized IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c) {
		final TLCStackFrame frame = new TLCStackFrame(stack.peek(), expr, c, tool);
		stack.push(frame);
		haltExecution(frame, this.stack.size());
		return this;
	}

	@Override
	public synchronized IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c, TLCState s) {
		final TLCStackFrame frame = new TLCStateStackFrame(stack.peek(), expr, c, tool, s);
		stack.push(frame);
		haltExecution(frame, this.stack.size());
		return this;
	}

	@Override
	public synchronized IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c, TLCState s,
			Action a, TLCState t) {
		final TLCStackFrame frame = new TLCActionStackFrame(stack.peek(), expr, c, tool, s, a, t);
		stack.push(frame);
		haltExecution(frame, this.stack.size());
		return this;
	}

	@Override
	public synchronized IDebugTarget pushFrame(TLCState s) {
		TLCStackFrame f = this.stack.peek();
		pushFrame(f.getTool(), f.getNode(), f.getContext(), s);
		return this;
	}

	@Override
	public synchronized IDebugTarget pushFrame(TLCState s, Action a, TLCState t) {
		TLCStackFrame f = this.stack.peek();
		return pushFrame(f.getTool(), f.getNode(), f.getContext(), s, a, t);
	}

	@Override
	public synchronized IDebugTarget popFrame(TLCState state) {
		TLCStackFrame f = this.stack.peek();
		return popFrame(f.getTool(), f.getNode(), f.getContext(), state);
	}

	@Override
	public synchronized IDebugTarget popFrame(TLCState s, TLCState t) {
		//TODO This swallows the predecessor!
		return popFrame(t);
	}

	@Override
	public synchronized IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c) {
		if (LOGGER.isLoggable(Level.FINER)) {
			LOGGER.finer(String.format("%s Call popFrame: [%s], level: %s\n",
					new String(new char[this.stack.size()]).replace('\0', '#'), expr, this.stack.size()));
		}
		final TLCStackFrame pop = stack.pop();
		assert expr == pop.getNode();
		return this;
	}

	@Override
	public synchronized IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, Value v) {
		popFrame(tool, expr, c);

		// Attach value to the parent (peeked) frame iff it matches the SemanticNode
		// from which v was evaluated.  It shouldn't be possible for peeked to be
		// null, but better be safe than sorry.
		final TLCStackFrame peeked = stack.peek();
		if (peeked != null && peeked.node.myUID == expr.myUID) {
			// Consider setting the value's source to expr iff it's null otherwise. However,
			// make sure that this doesn't introduce a regression because TLC branches
			// somewhere based on whether Value#hasSource is true.  If we are sure that
			// Value#hasSource is an invariant, tlc2.debug.TLCStackFrame.getStackVariables(List<Variable>)
			// could derive the variable's name via ((SyntaxTreeNode) v.getSource().getTreeNode()).getHumanReadableImage(),
			// which - in turn - would allow to attach values even to nodes where peeked.node.myUID != expr.myUID.
			// Not sure, if this is ever necessary though.
//			if (!v.hasSource()) {
//				// TLC's test suite doesn't produce an error/failure with v.setSource(expr).
//				v.setSource(expr);
//			}
			stack.peek().setValue(v);
		}
		return this;
	}

	@Override
	public synchronized IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, TLCState s) {
		final TLCStackFrame pop = stack.pop();
		assert expr == pop.getNode();
		return this;
	}

	@Override
	public synchronized IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, Value v, TLCState t) {
		popFrame(tool, expr, c, v);
		return this;
	}

	@Override
	public synchronized IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, TLCState s, TLCState t) {
		return popFrame(tool, expr, c);
	}

	@Override
	public synchronized IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, Value v, TLCState s, TLCState t) {
		popFrame(tool, expr, c, v);
		return this;
	}

	@Override
	public synchronized IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c, RuntimeException e) {
		return pushExceptionFrame(new TLCStackFrame(stack.peek(), expr, c, tool, e), e);
	}
	
	@Override
	public synchronized IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c,
			TLCState state, RuntimeException e) {
		return pushExceptionFrame(new TLCStateStackFrame(stack.peek(), expr, c, tool, state, e), e);
	}
	
	@Override
	public synchronized IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c, TLCState s,
			Action a, TLCState t, RuntimeException e) {
		return pushExceptionFrame(new TLCActionStackFrame(stack.peek(), expr, c, tool, s, a, t, e), e);
	}

	private IDebugTarget pushExceptionFrame(final TLCStackFrame frame, RuntimeException e) {
		stack.push(frame);

		// Let the client print the exception in its debug output UI.
		final OutputEventArguments oea = new OutputEventArguments();
		oea.setOutput(e.getMessage());
		if (launcher != null) {
			launcher.getRemoteProxy().output(oea);
			// Only halt the execution if a front-end/debugger is connect?
		}
		
		if (halt) {
			haltExecution(frame);
		}
		
		return this;
	}

	protected void haltExecution(final TLCStackFrame frame, final int level) {
		if (LOGGER.isLoggable(Level.FINER)) {
			LOGGER.finer(String.format("%s(%s): [%s]\n", new String(new char[level]).replace('\0', '#'), level, frame.getNode()));
		}
		if (matches(step, targetLevel, level) || matches(frame)) {
			haltExecution(frame);
		}
	}

	protected void haltExecution(final TLCStackFrame frame) {
		sendStopped(frame);

		try {
			// Halt TLC's evaluation by blocking on this (one-element) queue. The DAP
			// front-end will add an element that will unblock us.
			this.wait();
		} catch (InterruptedException notExpectedToHappen) {
			notExpectedToHappen.printStackTrace();
			java.lang.Thread.currentThread().interrupt();
		}
	}

	protected void sendStopped(final TLCStackFrame frame) {
		LOGGER.finer("loadSource -> stopped");
		if (launcher != null) {
			final StoppedEventArguments eventArguments = frame.getStoppedEventArgument();
			eventArguments.setThreadId(0);
			launcher.getRemoteProxy().stopped(eventArguments);
		}
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

	private boolean matches(final TLCStackFrame frame) {
		//TODO: Better match the location.  However, it shouldn't be done down here
		// but in setBreakpoints above that lets the debuggee tell the front-end
		// that a user-defined location is "corrected" to one that matches the bounds
		// of an expression in the semantic graph that is evaluated.  In other words,
		// setBreakpoints should traverse the semantic graph trying to find the smallest
		// i.e. best match for the given editor location.  The code here should then
		// simple compare the two location instances.
		// If no breakpoints are set, stream over an empty list.
		return breakpoints.getOrDefault(frame.getNode().getLocation().source(), new ArrayList<>()).stream()
				.anyMatch(b -> {
					return frame.matches(b);
				});
	}
	
	public static class Factory {

		public static TLCDebugger OVERRIDE;

		public static TLCDebugger getInstance(final boolean suspend, boolean halt) throws Exception {
			if (OVERRIDE != null) {
				return OVERRIDE;
			}
			if (suspend) {
				return new AttachingDebugger(Step.In, halt);
			}
			return new AttachingDebugger(Step.Continue, halt);
		}
	}
}
