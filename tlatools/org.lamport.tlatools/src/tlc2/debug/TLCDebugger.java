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
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Stack;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.eclipse.lsp4j.debug.Breakpoint;
import org.eclipse.lsp4j.debug.BreakpointLocation;
import org.eclipse.lsp4j.debug.BreakpointLocationsArguments;
import org.eclipse.lsp4j.debug.BreakpointLocationsResponse;
import org.eclipse.lsp4j.debug.CancelArguments;
import org.eclipse.lsp4j.debug.Capabilities;
import org.eclipse.lsp4j.debug.ConfigurationDoneArguments;
import org.eclipse.lsp4j.debug.ContinueArguments;
import org.eclipse.lsp4j.debug.ContinueResponse;
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
import org.eclipse.lsp4j.debug.launch.DSPLauncher;
import org.eclipse.lsp4j.debug.services.IDebugProtocolClient;
import org.eclipse.lsp4j.jsonrpc.Launcher;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;
import tlc2.TLCGlobals;
import tlc2.tool.EvalControl;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.DebugTool;
import tlc2.tool.impl.Tool;
import tlc2.util.Context;
import tlc2.util.FP64;
import tlc2.value.impl.Value;
import util.SimpleFilenameToStream;
import util.ToolIO;

public class TLCDebugger extends AbstractDebugger implements IDebugTarget {

	public static void main(String[] args) throws IOException, InterruptedException, ExecutionException {
		new TLCDebugger();
	}

	private Launcher<IDebugProtocolClient> launcher;

	public TLCDebugger() throws IOException, InterruptedException, ExecutionException {
		try (ServerSocket serverSocket = new ServerSocket(4712)) {
			while (true) {
				System.out.printf("Debugger is listening on localhost:%s", serverSocket.getLocalPort());
				final Socket socket = serverSocket.accept();
				final InputStream inputStream = socket.getInputStream();
				final OutputStream outputStream = socket.getOutputStream();

				launcher = DSPLauncher.createServerLauncher(this, inputStream, outputStream);
				launcher.startListening().get();
			}
		}
	}

	@Override
	public CompletableFuture<Capabilities> initialize(InitializeRequestArguments args) {
		System.out.println("initialize");

		Executors.newSingleThreadExecutor().submit(() -> {
			System.err.println("initialize -> initialized");
			// Signal the debugger that we are ready. It seem not relevant in what order the
			// response below and the initialized signal arrive at the debugger.
			launcher.getRemoteProxy().initialized();
		});

		// The capabilities define customizations how the debugger will interact with
		// this debuggee. Declaring no capabilities causes the most simple protocol to
		// be used.
		return CompletableFuture.completedFuture(new Capabilities());
	}

	@Override
	public CompletableFuture<Void> cancel(CancelArguments args) {
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<Void> configurationDone(ConfigurationDoneArguments args) {
		System.out.println("configurationDone");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<BreakpointLocationsResponse> breakpointLocations(BreakpointLocationsArguments args) {
		System.out.println("breakpointLocations");
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

	private volatile Breakpoint[] breakpoints;
	
	@Override
	public CompletableFuture<SetBreakpointsResponse> setBreakpoints(SetBreakpointsArguments args) {
		//TODO: Confirm breakpoint locations (see tlc2.debug.TLCDebugger.matches(SemanticNode))!!!
		System.out.println("setBreakpoints");
		SourceBreakpoint[] sbps = args.getBreakpoints();
		breakpoints = new Breakpoint[sbps.length];
		for (int j = 0; j < sbps.length; j++) {
			breakpoints[j] = new Breakpoint();
			breakpoints[j].setColumn(sbps[j].getColumn());
			breakpoints[j].setLine(sbps[j].getLine());
			breakpoints[j].setId(j);
			breakpoints[j].setVerified(true);
		}
		SetBreakpointsResponse response = new SetBreakpointsResponse();
		response.setBreakpoints(breakpoints);
		return CompletableFuture.completedFuture(response);
	}

	@Override
	public CompletableFuture<StackTraceResponse> stackTrace(StackTraceArguments args) {
		System.out.printf("stackTrace frame: %s, levels: %s\n", args.getStartFrame(), args.getLevels());

		final List<StackFrame> frames = new ArrayList<>(stack.size());
		for (int i = stack.size() - 1; i >= 0; i--) {
			final TLCStackFrame stackFrame = stack.elementAt(i);
			frames.add(stackFrame);
		}

		final StackTraceResponse res = new StackTraceResponse();
		res.setStackFrames(frames.toArray(new StackFrame[frames.size()]));
		return CompletableFuture.completedFuture(res);
	}

	@Override
	public CompletableFuture<ScopesResponse> scopes(ScopesArguments args) {
		System.out.printf("scopes frame %s\n", args.getFrameId());

		final ScopesResponse response = new ScopesResponse();

		stack.stream().filter(s -> s.getId() == args.getFrameId()).findFirst()
				.ifPresent(frame -> response.setScopes(frame.getScopes()));

		return CompletableFuture.completedFuture(response);
	}

	@Override
	public CompletableFuture<VariablesResponse> variables(VariablesArguments args) {
		final int vr = args.getVariablesReference();

		final VariablesResponse value = new VariablesResponse();
		
		final List<Variable> collect = this.stack.stream().map(frame -> frame.getVariables(vr)).flatMap(Stream::of)
				.collect(Collectors.toList());
		
		value.setVariables(collect.toArray(new Variable[collect.size()]));
		
		return CompletableFuture.completedFuture(value);
	}

	@Override
	public CompletableFuture<SetVariableResponse> setVariable(SetVariableArguments args) {
		System.out.println("setVariable");
		return CompletableFuture.completedFuture(new SetVariableResponse());
	}

	@Override
	public CompletableFuture<ThreadsResponse> threads() {
		System.out.println("threads");
		Thread thread = new Thread();
		thread.setId(0);
		thread.setName("worker");
		ThreadsResponse res = new ThreadsResponse();
		res.setThreads(new Thread[] { thread });
		return CompletableFuture.completedFuture(res);
	}

	@Override
	public CompletableFuture<ContinueResponse> continue_(ContinueArguments args) {
		System.out.println("continue_");
		targetLevel = -1;
		step = Step.Out;
		queue.offer(this);
		return CompletableFuture.completedFuture(new ContinueResponse());
	}

	@Override
	public CompletableFuture<Void> next(NextArguments args) {
		System.out.println("next/stepOver");
		step = Step.Over;
		queue.offer(this);
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<Void> stepIn(StepInArguments args) {
		System.out.println("stepIn");
		targetLevel++;
		step = Step.In;
		queue.offer(this);
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<Void> stepOut(StepOutArguments args) {
		System.out.println("stepOut");
		targetLevel--;
		step = Step.Out;
		queue.offer(this);
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<Void> pause(PauseArguments args) {
		System.out.println("pause");
		Executors.newSingleThreadExecutor().submit(() -> {
			System.err.println("pause -> stopped");
			StoppedEventArguments eventArguments = new StoppedEventArguments();
			eventArguments.setThreadId(0);
			eventArguments.setReason("pause");
			launcher.getRemoteProxy().stopped(eventArguments);
		});
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<Void> launch(Map<String, Object> args) {
		System.out.println("launch");

		final Path p = Paths.get((String) args.get("program"));
		final String specPath = p.getParent().toAbsolutePath().toString();
		final String specName = p.getFileName().toFile().toString();
		final String moduleName = specName.replaceFirst(".tla$", "");

		// IValue#hashCode calls below require fingerprints to be correctly initialized.
		FP64.Init();

		// Listen to that SANY and TLC have to say, and what gets written with TLC!Print*.
		ToolIO.out = new PrintStream(System.out) {
			@Override
			public void println(String str) {
				this.print(str + "\n");
			}
			@Override
			public void print(String str) {
				super.print(str);
				final OutputEventArguments oea = new OutputEventArguments();
				oea.setOutput(str);
				launcher.getRemoteProxy().output(oea);
			}
		};
		ToolIO.reset();
		
		final Tool tool = new DebugTool(moduleName, specName, new SimpleFilenameToStream(specPath), this);
		final ModuleNode module = tool.getSpecProcessor().getRootModule();
		// The spec has to have an "debugMe" operator.
		final OpDefNode valueNode = module.getOpDef("debugMe");

		// Make sure we pause/stop debugging initially.
		targetLevel = Integer.MIN_VALUE;
		step = Step.In;

		// Kick off the evaluation of the expression in Tool in a different thread.
		Executors.newSingleThreadExecutor().submit(() -> {
			// Expanding values causes them to be un-lazied/enumerated, which we don't want
			// as a side-effect of the debugger.
			TLCGlobals.expand = false;
			
			tool.eval(valueNode.getBody(), Context.Empty, TLCState.Empty, TLCState.Empty, EvalControl.Debug,
					CostModel.DO_NOT_RECORD);
		});

		return CompletableFuture.completedFuture(null);
	}

	// 8888888888888888888888888888888888888888888888888888888888888888888888888 //

	//TODO: Instead of maintaining the stack here, we could evaluated with CallStackTool
	// that will get the job done for us (tlc2.tool.impl.CallStackTool.callStack).
	// However, CST only keeps the SemanticNode but skips the Context and the values. We
	// would have to make CST take a function that applies a transformation for the debugger
	// and a different one when CST does its original job.
	private final Stack<TLCStackFrame> stack = new Stack<>();

	//TODO: This is a clutch; it's working but should be simplified!
	private final ArrayBlockingQueue<IDebugTarget> queue = new ArrayBlockingQueue<>(1);
	private volatile int targetLevel;
	private volatile Step step;

	@Override
	public IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c, int control) {
		final int level = this.stack.size();
		System.out.printf("%s Call pushFrame: [%s], level: %s\n", new String(new char[level]).replace('\0', '#'), expr,
				level);

		stack.push(new TLCStackFrame(expr, c, tool));

		pushFrame(expr, level);
		return this;
	}

	@Override
	public IDebugTarget pushFrame(Tool tool, SemanticNode expr, Context c, TLCState ps) {
		final int level = this.stack.size();
		stack.push(new TLCStateStackFrame(expr, c, tool, ps));
		pushFrame(expr, level);
		return this;
	}

	private void pushFrame(SemanticNode expr, final int level) {
		if (matches(step, targetLevel, level) || matches(expr)) {
			System.err.println("loadSource -> stopped");
			StoppedEventArguments eventArguments = new StoppedEventArguments();
			eventArguments.setThreadId(0);
			launcher.getRemoteProxy().stopped(eventArguments);

			try {
				queue.take();
			} catch (InterruptedException notExpectedToHappen) {
				notExpectedToHappen.printStackTrace();
				java.lang.Thread.currentThread().interrupt();
			}
		}
	}

	@Override
	public IDebugTarget pushFrame(TLCState state) {
		TLCStackFrame f = this.stack.peek();
		pushFrame(f.getTool(), f.getNode(), f.getContext(), state);
		return this;
	}

	@Override
	public IDebugTarget popFrame(TLCState state) {
		TLCStackFrame f = this.stack.peek();
		popFrame(f.getTool(), f.getNode(), f.getContext(), state);
		return this;
	}

	@Override
	public IDebugTarget popFrame(Tool tool, Value v, SemanticNode expr, Context c, int control) {
		final int level = this.stack.size();
		System.out.printf("%s Call popFrame: [%s], level: %s\n", new String(new char[level]).replace('\0', '#'), expr,
				level);
		final TLCStackFrame pop = stack.pop();
		assert expr == pop.getNode();
		return this;
	}

	@Override
	public IDebugTarget popFrame(Tool tool, SemanticNode expr, Context c, TLCState ps) {
		final TLCStackFrame pop = stack.pop();
		assert expr == pop.getNode();
		return this;
	}

	// TODO: This is only working more or less for step.in.
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
			// When stepping out, level has to greater than or zero/0;
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
		return Arrays.asList(breakpoints).stream().anyMatch(b -> b.getLine() == location.beginLine());
	}
}
