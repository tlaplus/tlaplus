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

import java.util.Map;
import java.util.concurrent.CompletableFuture;

import org.eclipse.lsp4j.debug.BreakpointLocationsArguments;
import org.eclipse.lsp4j.debug.BreakpointLocationsResponse;
import org.eclipse.lsp4j.debug.CompletionsArguments;
import org.eclipse.lsp4j.debug.CompletionsResponse;
import org.eclipse.lsp4j.debug.DataBreakpointInfoArguments;
import org.eclipse.lsp4j.debug.DataBreakpointInfoResponse;
import org.eclipse.lsp4j.debug.DisassembleArguments;
import org.eclipse.lsp4j.debug.DisassembleResponse;
import org.eclipse.lsp4j.debug.DisconnectArguments;
import org.eclipse.lsp4j.debug.GotoArguments;
import org.eclipse.lsp4j.debug.LoadedSourcesArguments;
import org.eclipse.lsp4j.debug.LoadedSourcesResponse;
import org.eclipse.lsp4j.debug.ModulesArguments;
import org.eclipse.lsp4j.debug.ModulesResponse;
import org.eclipse.lsp4j.debug.ReadMemoryArguments;
import org.eclipse.lsp4j.debug.ReadMemoryResponse;
import org.eclipse.lsp4j.debug.RestartArguments;
import org.eclipse.lsp4j.debug.RestartFrameArguments;
import org.eclipse.lsp4j.debug.ReverseContinueArguments;
import org.eclipse.lsp4j.debug.RunInTerminalRequestArguments;
import org.eclipse.lsp4j.debug.RunInTerminalResponse;
import org.eclipse.lsp4j.debug.SetDataBreakpointsArguments;
import org.eclipse.lsp4j.debug.SetDataBreakpointsResponse;
import org.eclipse.lsp4j.debug.SetExceptionBreakpointsArguments;
import org.eclipse.lsp4j.debug.SetExpressionArguments;
import org.eclipse.lsp4j.debug.SetExpressionResponse;
import org.eclipse.lsp4j.debug.SetFunctionBreakpointsArguments;
import org.eclipse.lsp4j.debug.SetFunctionBreakpointsResponse;
import org.eclipse.lsp4j.debug.SetInstructionBreakpointsArguments;
import org.eclipse.lsp4j.debug.SetInstructionBreakpointsResponse;
import org.eclipse.lsp4j.debug.SourceArguments;
import org.eclipse.lsp4j.debug.SourceResponse;
import org.eclipse.lsp4j.debug.StepBackArguments;
import org.eclipse.lsp4j.debug.StepInTargetsArguments;
import org.eclipse.lsp4j.debug.StepInTargetsResponse;
import org.eclipse.lsp4j.debug.TerminateArguments;
import org.eclipse.lsp4j.debug.TerminateThreadsArguments;
import org.eclipse.lsp4j.debug.services.IDebugProtocolServer;

public abstract class AbstractDebugger implements IDebugProtocolServer{

	@Override
	public CompletableFuture<SourceResponse> source(SourceArguments args) {
		System.out.println("SourceResponse");
		return CompletableFuture.completedFuture(new SourceResponse());
	}

	@Override
	public CompletableFuture<LoadedSourcesResponse> loadedSources(LoadedSourcesArguments args) {
		System.out.println("loadedSources");
		return CompletableFuture.completedFuture(new LoadedSourcesResponse());
	}

	@Override
	public CompletableFuture<Void> stepBack(StepBackArguments args) {
		System.out.println("stepBack");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<Void> goto_(GotoArguments args) {
		System.out.println("goto_");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<Void> attach(Map<String, Object> args) {
		System.out.println("attach");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<Void> restart(RestartArguments args) {
		System.out.println("restart");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<Void> disconnect(DisconnectArguments args) {
		System.out.println("disconnect");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<Void> terminate(TerminateArguments args) {
		System.out.println("terminate");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<RunInTerminalResponse> runInTerminal(RunInTerminalRequestArguments args) {
		System.out.println("runInTerminal");
		return CompletableFuture.completedFuture(new RunInTerminalResponse());
	}

	@Override
	public CompletableFuture<SetFunctionBreakpointsResponse> setFunctionBreakpoints(
			SetFunctionBreakpointsArguments args) {
		System.out.println("setFunctionBreakpoint");
		return CompletableFuture.completedFuture(new SetFunctionBreakpointsResponse());
	}

	@Override
	public CompletableFuture<Void> setExceptionBreakpoints(SetExceptionBreakpointsArguments args) {
		System.out.println("setExceptionBreakpoints");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<DataBreakpointInfoResponse> dataBreakpointInfo(DataBreakpointInfoArguments args) {
		System.out.println("dataBreakpointInfo");
		return CompletableFuture.completedFuture(new DataBreakpointInfoResponse());
	}

	@Override
	public CompletableFuture<SetDataBreakpointsResponse> setDataBreakpoints(SetDataBreakpointsArguments args) {
		System.out.println("setDataBreakpoints");
		return CompletableFuture.completedFuture(new SetDataBreakpointsResponse());
	}

	@Override
	public CompletableFuture<SetInstructionBreakpointsResponse> setInstructionBreakpoints(
			SetInstructionBreakpointsArguments args) {
		System.out.println("setInstructionBreakpoints");
		return CompletableFuture.completedFuture(new SetInstructionBreakpointsResponse());
	}

	@Override
	public CompletableFuture<Void> terminateThreads(TerminateThreadsArguments args) {
		System.out.println("terminateThreads");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<ModulesResponse> modules(ModulesArguments args) {
		System.out.println("ModulesResponse");
		return CompletableFuture.completedFuture(new ModulesResponse());
	}

	@Override
	public CompletableFuture<Void> reverseContinue(ReverseContinueArguments args) {
		System.out.println("reverseContinue");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<Void> restartFrame(RestartFrameArguments args) {
		System.out.println("restartFrame");
		return CompletableFuture.completedFuture(null);
	}

	@Override
	public CompletableFuture<SetExpressionResponse> setExpression(SetExpressionArguments args) {
		System.out.println("setExpression");
		return CompletableFuture.completedFuture(new SetExpressionResponse());
	}

	@Override
	public CompletableFuture<StepInTargetsResponse> stepInTargets(StepInTargetsArguments args) {
		System.out.println("stepInTargets");
		return CompletableFuture.completedFuture(new StepInTargetsResponse());
	}

	@Override
	public CompletableFuture<CompletionsResponse> completions(CompletionsArguments args) {
		System.out.println("completions");
		return CompletableFuture.completedFuture(new CompletionsResponse());
	}

	@Override
	public CompletableFuture<ReadMemoryResponse> readMemory(ReadMemoryArguments args) {
		System.out.println("readMemory");
		return CompletableFuture.completedFuture(new ReadMemoryResponse());
	}

	@Override
	public CompletableFuture<DisassembleResponse> disassemble(DisassembleArguments args) {
		System.out.println("disassemble");
		return CompletableFuture.completedFuture(new DisassembleResponse());
	}

	@Override
	public synchronized CompletableFuture<BreakpointLocationsResponse> breakpointLocations(BreakpointLocationsArguments args) {
		System.out.println("breakpointLocations");
		// https://microsoft.github.io/debug-adapter-protocol/specification#Requests_BreakpointLocations
		// Requires Capabilities#setSupportBreakpointLocationsRequest(true) to be returned in TLCDebugger.initialize(..).
		return CompletableFuture.completedFuture(new BreakpointLocationsResponse());
	}
}
