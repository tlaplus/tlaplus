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

import java.io.IOException;
import java.io.PipedOutputStream;
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
import org.eclipse.lsp4j.debug.CapabilitiesEventArguments;
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
import org.eclipse.lsp4j.debug.OutputEventArgumentsCategory;
import org.eclipse.lsp4j.debug.PauseArguments;
import org.eclipse.lsp4j.debug.ReverseContinueArguments;
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
import org.eclipse.lsp4j.debug.StepBackArguments;
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
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tlc2.TLCGlobals;
import tlc2.tool.Action;
import tlc2.tool.INextStateFunctor;
import tlc2.tool.StatefulRuntimeException;
import tlc2.tool.TLCState;
import tlc2.tool.impl.DebugTool;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.value.impl.Value;

public abstract class TLCDebugger extends AbstractDebugger implements IDebugTarget {
	protected static Logger LOGGER = Logger.getLogger(TLCDebugger.class.getName());

	protected PipedOutputStream pipedOutputStream;
	protected Launcher<IDebugProtocolClient> launcher;

	private Tool tool;

	public TLCDebugger() {
		this.step = Step.In;
		this.haltExp = true;
		this.haltInv = true;
	}

	public TLCDebugger(final Step s, final boolean halt) {
		this.step = s;
		this.haltExp = halt;
		this.haltInv = halt;
	}

	/*
	 * Unit testing only!!!
	 */
	TLCDebugger(final Step s, final boolean halt, final boolean executionIsHalted) {
		this.step = s;
		this.haltExp = halt;
		this.haltInv = halt;
		this.executionIsHalted = executionIsHalted;
	}

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
		// introduces this message implements the request. We learned that EI are only
		// useful if we wish to show the Java stack trace (which users don't care about).
		// In a nutshell, the debugger backend can return a ExceptionInfoResponse that
		// has additional field compared to the generic exception handling mechanisms.
		// These additional fields cause the VSCode zone widget (area dynamically made
		// visible in the editor upon an exception) to have a richer formatting.
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
		// TODO: Implement stepping back for model-checking and simulation/generation.
		// Stepping back would be hugely useful especially because TLC's evaluation behavior might be 
		// surprising (non-determinism). This can cause users to miss the stack-frame they wish to see.
		// Implementing arbitrary navigation along stack-frames is impossible unless one implements
		// undo operations for each Tool action.  However, it should be good enough to reset Tool
		// to e.g. the beginning of the evaluation of the next-state relation for state s, evaluation
		// of the invariant for state s, evaluation of state- & action-constraints for s, ... by
		// throwing a ResetEvalException.
		// With support set to true, the debugger front-end shows two additional button
		// "Step Back" and "Reverse", which are mapped to the methods stepBack and
		// reverseContinue below.
		capabilities.setSupportsStepBack(true);
		
		// https://github.com/Microsoft/vscode/issues/28025
		// TODO: This seems to be the way to add commands to the front-end's variable
		// view. Commands that could be useful are (Json) exporters for the trace, ...
		capabilities.setSupportsValueFormattingOptions(false);
		
		// Stepping granularity changes the behavior of next, step-in, step-out, ...
		// s.t. a step get re-defined from source-level to machine-instruction level. It
		// is a recent addition to the DAP (1.41.x https://microsoft.github.io/debug-adapter-protocol/changelog).
		// While not being tailored to state-based formalism such as TLA+, it can
		// probably be retrofitted for our purposes (think machine-instruction is
		// instead defined to be a TLA+ state). However, the debugger front-end (VSCode)
		// doesn't have the necessary UI to let users change the stepping granularity:
		// https://github.com/microsoft/vscode/issues/102236
		// https://cs.github.com/microsoft/vscode/blob/4b9253809f3fd3bc21c19cd5e19e02d211656e66/src/vs/workbench/contrib/debug/common/debug.ts?q=repo%3Amicrosoft%2Fvscode+Granul#L437
		// https://github.com/microsoft/vscode-mock-debug/blob/12b05dc0d9ae5a41a6f5548ded9e6db73273bfbc/src/mockDebug.ts
		capabilities.setSupportsSteppingGranularity(false);

		// A GotoTarget describes a code location that can be used as a target in the
		// ‘goto’ request. GotoTarget support lets the debugger (backend) send locations
		// to the front-end that VSCode only seems to show in the command emmet as a
		// result of the Goto Target command.
		// https://microsoft.github.io/debug-adapter-protocol/specification#Types_GotoTarget
		capabilities.setSupportsGotoTargetsRequest(false);
		
		// When data breakpoints are supported, users can add breakpoints that fire when
		// the value of a variable changes. To create data breakpoints, users
		// right-click variables in the front-end's variable view and select data breakpoint
		// from the context menu.
		// If a debugger supports data breakpoints, they can be set from the VARIABLES
		// view and will get hit when the value of the underlying variable changes. Data
		// breakpoints are shown with a red hexagon in the BREAKPOINTS section.
		// https://code.visualstudio.com/docs/editor/debugging#_data-breakpoints
		capabilities.setSupportsDataBreakpoints(false);

		// Users create function breakpoints from the "Breakpoints" view of the debugger
		// front-end by clicking the view menu's "+" button, and entering a function's
		// name into a free-form field.
		// Instead of placing breakpoints directly in source code, a debugger can
		// support creating breakpoints by specifying a function name. This is useful in
		// situations where source is not available but a function name is known. A
		// function breakpoint is created by pressing the + button in the BREAKPOINTS
		// section header and entering the function name. Function breakpoints are shown
		// with a red triangle in the BREAKPOINTS section.
		// https://code.visualstudio.com/docs/editor/debugging#_function-breakpoints
		capabilities.setSupportsFunctionBreakpoints(false);
		
		// I couldn't figure out how instruction breakpoints work. Presumably, an
		// instruction breakpoint is related to the DAP's assembly feature when the
		// source code gets replaced with machine instructions or bytecode during
		// debugging.  With TLA+, the semantic graph that is evaluated by TLC could
		// be defined our assembly.  However, a graph is probably not too useful when
		// shown in a text editor.
		capabilities.setSupportsInstructionBreakpoints(false);
		capabilities.setSupportsDisassembleRequest(false);
		
		// When Clipboard is supported, the evaluate method can be called with the
		// EvaluateArgumentsContext.CLIPBOARD argument.  We could use it to re-format
		// a variable to json, ...
		capabilities.setSupportsClipboardContext(true);
		
		return CompletableFuture.completedFuture(capabilities);
	}

	private ExceptionBreakpointsFilter[] getExceptionBreakpointFilters() {
		final ExceptionBreakpointsFilter filter = new ExceptionBreakpointsFilter();
		filter.setDefault_(this.haltExp);
		filter.setFilter("ExceptionBreakpointsFilter");
		filter.setLabel("Halt (break) on exceptions");

		if (TLCGlobals.mainChecker != null) {
			// Halting on violations/invariants does not work with exhaustive search.
			// See the following two git commit for why:
			// e81e1e2b19b7a03f74d245cac009e84a0415e45d
			// 42f251546ce99c19f1a7a44310816527a15ade2b
			return new ExceptionBreakpointsFilter[] { filter };
		} else {
			final ExceptionBreakpointsFilter violations = new ExceptionBreakpointsFilter();
			violations.setDefault_(this.haltInv);
			violations.setFilter("InvariantBreakpointsFilter");
			violations.setLabel("Halt (break) on violations");

			return new ExceptionBreakpointsFilter[] { filter, violations };
		}
	}

	@Override
	public synchronized CompletableFuture<Void> setExceptionBreakpoints(SetExceptionBreakpointsArguments args) {
		final List<String> asList = Arrays.asList(args.getFilters());
		this.haltExp = asList.contains("ExceptionBreakpointsFilter");
		this.haltInv = asList.contains("InvariantBreakpointsFilter");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public synchronized CompletableFuture<EvaluateResponse> evaluate(final EvaluateArguments args) {
		// See https://github.com/alygin/vscode-tlaplus/blob/master/src/main.ts
		if (EvaluateArgumentsContext.HOVER.equals(args.getContext()) && args.getExpression().startsWith("tlaplus://")) {
			return CompletableFuture.completedFuture(this.stack.stream().filter(f -> f.getId() == args.getFrameId())
					.findAny().map(f -> f.get(args)).orElse(new EvaluateResponse()));
		} else if (EvaluateArgumentsContext.REPL.equals(args.getContext())) {
			if ("violate".equalsIgnoreCase(args.getExpression())) {
				DebugTool.setForceViolation();
				return CompletableFuture.completedFuture(new EvaluateResponse());
			}
			// TODO: Users can enter (arbitrary) expressions in the front-end's "Debug
			// Console". We could try to handle valid TLA+ expressions here, but SANY
			// unfortunately lacks incremental parsing.  Study related discussion started
			// in http://discuss.tlapl.us/msg01427.html and continued offline in the involved
			// inboxes.
			// This is a poor-man's version of debugger commands:
			// https://github.com/microsoft/debug-adapter-protocol/issues/231
			// https://github.com/microsoft/debug-adapter-protocol/issues/216
			try {
				pipedOutputStream.write((args.getExpression() + "\n").getBytes());
			} catch (IOException notExpectedToHappen) {
				notExpectedToHappen.printStackTrace();
			}
		} else if ("variables".equals(args.getContext())) {
			// The front-end passes "variables" as the context when users select a variable
			// in the variables view and invoke the copy-to-clipboard action. Since the
			// variables view shows the plain TLA+ values, we don't have to do anything
			// here, but simply return the value. One thing to investigate is why
			// copy-to-clipboard requires a full front-end/back-end round-trip in the first
			// place. I suspect that this is a side-effect of the
			// setSupportsEvaluateForHovers capability that the back-end announces in
			// initialize above. 
			// TODO Our version of LSP4J doesn't know the constant "variables" yet, which is
			// why it's hard-coded here.
			final EvaluateResponse response = new EvaluateResponse();
			response.setResult(args.getExpression());
			return CompletableFuture.completedFuture(response);
		} else if ("watch".equals(args.getContext())) {
			return CompletableFuture.completedFuture(this.stack.stream().filter(f -> f.getId() == args.getFrameId())
					.findAny().map(f -> f.getWatch(args.getExpression())).orElse(new EvaluateResponse()));
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
		haltExp = false;
		haltInv = false;
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
				
				final Action nextPred = tool.getSpecProcessor().getNextPred();
				final Location loc = nextPred.getDefinition();
				if (loc.includes(sbp.getLocation()) && sbp.getHits() > 0) {
					// see tlc2.debug.TLCStepActionStackFrame.matches(TLCSourceBreakpoint)
					breakpoint.setVerified(false);
					breakpoint.setMessage("A Next breakpoint does not support a hit condition.");
				}
				
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
		
		if (!executionIsHalted) {
			// Returning the current stack frames to the front-end when execution is *not*
			// halted causes the front-end to briefly jump to the location of the topmost
			// stack frame.
			res.setStackFrames(new StackFrame[0]);
			res.setTotalFrames(0);
			return CompletableFuture.completedFuture(res);
		}

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
		
		if (!stack.isEmpty() && stack.peek().handle(this)) {
			return this.stack.peek().continue_(this);
		}

		targetLevel = -1;
		step = Step.Continue;
		this.notify();
		return CompletableFuture.completedFuture(new ContinueResponse());
	}

	@Override
	public synchronized CompletableFuture<Void> next(NextArguments args) {
		LOGGER.finer("next/stepOver");
		
		if (!stack.isEmpty() && stack.peek().handle(this)) {
			return this.stack.peek().stepOver(this);
		}

		targetLevel = this.stack.size();
		step = Step.Over;
		this.notify();
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public synchronized CompletableFuture<Void> stepIn(StepInArguments args) {
		LOGGER.finer("stepIn");
		
		if (!stack.isEmpty() && stack.peek().handle(this)) {
			return this.stack.peek().stepIn(this);
		}
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

		if (!stack.isEmpty() && stack.peek().handle(this)) {
			return this.stack.peek().stepOut(this);
		}
		
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
	
	@Override
	public synchronized CompletableFuture<Void> stepBack(StepBackArguments args) {
		LOGGER.finer("stepBack");

		if (!stack.isEmpty() && stack.peek().handle(this)) {
			return this.stack.peek().stepBack(this);
		}

		step = Step.Reset;
		this.notify();

		return CompletableFuture.completedFuture(null);
	}

	@Override
	public synchronized CompletableFuture<Void> reverseContinue(ReverseContinueArguments args) {
		LOGGER.finer("reverseContinue");
		
		if (!stack.isEmpty() && stack.peek().handle(this)) {
			return this.stack.peek().reverseContinue(this);
		}
		
		step = Step.Reset_Start;
		this.notify();

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
	private volatile Granularity granularity = Granularity.Formula;
	
	private volatile boolean haltExp;
	private volatile boolean haltInv;

	private volatile boolean executionIsHalted = false;
	
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
	public synchronized StepDirection pushFrame(Tool tool, OpDefNode expr, Context c, TLCState s,
			Action a, INextStateFunctor fun) {
		final TLCSuccessorsStackFrame frame = new TLCSuccessorsStackFrame(stack.peek(), expr, c, tool, s, a, fun);
		stack.push(frame);
		haltExecution(frame, this.stack.size());
		return frame.getDirection();
	}

	@Override
	public synchronized IDebugTarget popFrame(Tool tool, OpDefNode expr, Context c, TLCState s, Action a,
			INextStateFunctor fun) {
		final TLCStackFrame frame = this.stack.peek();
		if (frame != null && matches(frame)) {
			// Check if execution/evaluation should be halted even if fun#getStates is
			// empty.  Users can set the hit count to >0 to ignore non-enabled actions
			haltExecution(frame);
		}
		return popFrame(s);
	}

	@Override
	public synchronized IDebugTarget pushFrame(TLCState s) {
		TLCStackFrame f = this.stack.peek();
		pushFrame(f.getTool(), f.getNode(), f.getContext(), s);
		return this;
	}

	@Override
	public synchronized StepDirection pushFrame(TLCState s, Action a, TLCState t) {
		final TLCStepActionStackFrame frame = new TLCStepActionStackFrame(this.stack.peek(), tool, s, a, t);
		stack.push(frame);
		haltExecution(frame, this.stack.size());
		return frame.getStepDirection(); // Note different return type here!
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
		assert pop.matches(expr);
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
		assert pop.matches(expr);
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
	public synchronized IDebugTarget popExceptionFrame(Tool tool, SemanticNode expr, Context c, Value v, StatefulRuntimeException e) {
		if (LOGGER.isLoggable(Level.FINER)) {
			LOGGER.finer(String.format("%s Call popExceptionFrame: [%s], level: %s\n",
					new String(new char[this.stack.size()]).replace('\0', '#'), expr, this.stack.size()));
		}
		final TLCStackFrame pop = stack.pop();
		assert pop.matches(expr, e);
		return this;
	}

	@Override
	public synchronized IDebugTarget popExceptionFrame(Tool tool, SemanticNode expr, Context c, Value v, TLCState s, StatefulRuntimeException e) {
		return popExceptionFrame(tool, expr, c, v, e);
	}

	@Override
	public synchronized IDebugTarget popExceptionFrame(Tool tool, SemanticNode expr, Context c, Value v, TLCState s, TLCState t, StatefulRuntimeException e) {
		return popExceptionFrame(tool, expr, c, v, e);
	}
	
	private boolean exceptionNotYetHandled(final StatefulRuntimeException e) {
		// The debugger handles an exception such as
		// EvalException/TLCRuntimeException/InvariantViolationException) (close to) the
		// call-site in Tool to point users to the most specific location. However, the
		// exception also gets re-thrown for TLC's generic exception handling to deal
		// with it. Potentially, this causes the debugger to catch the same exception
		// again when it travels up Tool's call-stack.  Here, we make sure that the debugger
		// handles an exception only once.
		return !e.setKnown();
	}
	
	@Override
	public synchronized IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c, StatefulRuntimeException e) {
		if (exceptionNotYetHandled(e)) {
			return pushFrameAndHalt(haltExp, new TLCStackFrame(stack.peek(), expr, c, tool, e), e);
		}
		return this;
	}
	
	@Override
	public synchronized IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c,
			TLCState state, StatefulRuntimeException e) {
		if (exceptionNotYetHandled(e)) {
			return pushFrameAndHalt(haltExp, new TLCStateStackFrame(stack.peek(), expr, c, tool, state, e), e);
		}
		return this;
	}
	
	@Override
	public synchronized IDebugTarget pushExceptionFrame(Tool tool, SemanticNode expr, Context c, TLCState s,
			Action a, TLCState t, StatefulRuntimeException e) {
		if (exceptionNotYetHandled(e)) {
			return pushFrameAndHalt(haltExp, new TLCActionStackFrame(stack.peek(), expr, c, tool, s, a, t, e), e);
		}
		return this;
	}

	@Override
	public synchronized IDebugTarget popExceptionFrame(Tool tool, SemanticNode expr, Context c, TLCState s,
			Action a, TLCState t, StatefulRuntimeException e) {
		return popExceptionFrame(tool, expr, c, null, e);
	}

	@Override
	public synchronized IDebugTarget markInvariantViolatedFrame(Tool debugTool, SemanticNode expr, Context c, TLCState predecessor, Action a, TLCState state, StatefulRuntimeException e) {
		if (exceptionNotYetHandled(e)) {
			pushFrameAndHalt(haltInv, new TLCActionStackFrame(stack.peek(), expr, c, tool, predecessor, a, state, e), e);
		}
		return this;
	}

	@Override
	public synchronized IDebugTarget markAssumptionViolatedFrame(Tool debugTool, SemanticNode expr, Context c) {
		final TLCStackFrame frame = new TLCStackFrame(null, expr, c, tool); // no parent!
		stack.push(frame);
		if (haltInv) {
			haltExecution(frame);
		}
		return this;
	}

	private IDebugTarget pushFrameAndHalt(final boolean halt, final TLCStackFrame frame, final RuntimeException e) {
		// Calling methods duplicate the top-most stack-frame with the exception causes
		// the front-end to raise a corresponding error in the editor.
		
		stack.push(frame);

		// Let the client print the exception in its debug output UI (Debug Console in
		// VSCode). However, only halt the execution if a front-end/debugger is connect?
		if (launcher != null) {
			final OutputEventArguments oea = new OutputEventArguments();
			oea.setOutput(e.getMessage() == null ? "" : e.getMessage());
			// A hyperlink pointing to the given location is placed right of the output in
			// the Debug Console.
			oea.setLine(frame.getLine());
			oea.setColumn(frame.getColumn());
			oea.setSource(frame.getSource());
			// STDERR get colored red in VSCode's Debug Console.
			// (stdout -> blue, console -> orange)
			oea.setCategory(OutputEventArgumentsCategory.STDERR);
			launcher.getRemoteProxy().output(oea);
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
		if (matches(step, targetLevel, level)) {
			haltExecution(frame);
		} else if (matches(frame)) {
			// Calling pre/postHalt because stack frame decided to halt and might want to do
			// something specific. It does not giving control to the frame in the if branch
			// because the frame wasn't involved in the decision to halt.
			frame.preHalt(this);
			haltExecution(frame);
			frame.postHalt(this);
		}
	}

	protected void haltExecution(final TLCStackFrame frame) {
		sendStopped(frame);

		try {
			// Halt TLC's evaluation by blocking the worker thread. This state is observable
			// externally through the value of executionIsHalted.
			executionIsHalted = true;
			this.wait();
			executionIsHalted = false;
		} catch (InterruptedException notExpectedToHappen) {
			notExpectedToHappen.printStackTrace();
			java.lang.Thread.currentThread().interrupt();
		}
		
		if (Step.Reset == step) {
			step = Step.In;
			if (frame.parent != null) {
				// If frame has no parent, there is nothing the debugger reset to--it marks the entry point of the evaluation.
				throw new ResetEvalException(frame.parent);
			}
		} else if (Step.Reset_Start == step) {
			step = Step.In;
			// TODO: stack#getLast always takes us to the top-most frame (usually a
			// TLCSuccessorStackFrame). However, this is not the best target if, e.g., the a
			// user reverses an invariant. In this case, the debugger should reverse to the
			// beginning of the invariant and not the beginning of the next-state relation.
			// Idea: When creating stack frames, mark those that are meaningful targets to
			// reverse back to.  Here, we would traverse the stack to find the first one of
			// those targets.
			throw new ResetEvalException(stack.getLast());
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

	protected void sendCapabilities(final Capabilities capabilities) {
		LOGGER.finer("sendCapabilities");
		if (launcher != null) {
			final CapabilitiesEventArguments cea = new CapabilitiesEventArguments();
			cea.setCapabilities(capabilities);
			launcher.getRemoteProxy().capabilities(cea);
		}
	}

	public void setGranularity(Granularity g) {
		this.granularity = g;
	}

	public Granularity getGranularity() {
		return this.granularity;
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

		public static TLCDebugger getInstance(final int port, final boolean suspend, boolean halt) throws Exception {
			if (OVERRIDE != null) {
				return OVERRIDE;
			}
			if (suspend) {
				return new AttachingDebugger(port, Step.In, halt);
			}
			return new AttachingDebugger(port, Step.Continue, halt);
		}
	}
}
