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

import org.eclipse.lsp4j.debug.*;
import org.eclipse.lsp4j.debug.services.IDebugProtocolServer;

import java.util.Map;
import java.util.concurrent.CompletableFuture;

public abstract class AbstractDebugger implements IDebugProtocolServer {

    @Override
    public CompletableFuture<SourceResponse> source(final SourceArguments args) {
        System.out.println("SourceResponse");
        return CompletableFuture.completedFuture(new SourceResponse());
    }

    @Override
    public CompletableFuture<LoadedSourcesResponse> loadedSources(final LoadedSourcesArguments args) {
        System.out.println("loadedSources");
        return CompletableFuture.completedFuture(new LoadedSourcesResponse());
    }

    @Override
    public CompletableFuture<Void> stepBack(final StepBackArguments args) {
        System.out.println("stepBack");
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<Void> goto_(final GotoArguments args) {
        System.out.println("goto_");
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<Void> attach(final Map<String, Object> args) {
        System.out.println("attach");
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<Void> restart(final RestartArguments args) {
        System.out.println("restart");
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<Void> disconnect(final DisconnectArguments args) {
        System.out.println("disconnect");
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<Void> terminate(final TerminateArguments args) {
        System.out.println("terminate");
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<RunInTerminalResponse> runInTerminal(final RunInTerminalRequestArguments args) {
        System.out.println("runInTerminal");
        return CompletableFuture.completedFuture(new RunInTerminalResponse());
    }

    @Override
    public CompletableFuture<SetFunctionBreakpointsResponse> setFunctionBreakpoints(
            final SetFunctionBreakpointsArguments args) {
        System.out.println("setFunctionBreakpoint");
        return CompletableFuture.completedFuture(new SetFunctionBreakpointsResponse());
    }

    @Override
    public CompletableFuture<Void> setExceptionBreakpoints(final SetExceptionBreakpointsArguments args) {
        System.out.println("setExceptionBreakpoints");
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<DataBreakpointInfoResponse> dataBreakpointInfo(final DataBreakpointInfoArguments args) {
        System.out.println("dataBreakpointInfo");
        return CompletableFuture.completedFuture(new DataBreakpointInfoResponse());
    }

    @Override
    public CompletableFuture<SetDataBreakpointsResponse> setDataBreakpoints(final SetDataBreakpointsArguments args) {
        System.out.println("setDataBreakpoints");
        return CompletableFuture.completedFuture(new SetDataBreakpointsResponse());
    }

    @Override
    public CompletableFuture<SetInstructionBreakpointsResponse> setInstructionBreakpoints(
            final SetInstructionBreakpointsArguments args) {
        System.out.println("setInstructionBreakpoints");
        return CompletableFuture.completedFuture(new SetInstructionBreakpointsResponse());
    }

    @Override
    public CompletableFuture<Void> terminateThreads(final TerminateThreadsArguments args) {
        System.out.println("terminateThreads");
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<ModulesResponse> modules(final ModulesArguments args) {
        System.out.println("ModulesResponse");
        return CompletableFuture.completedFuture(new ModulesResponse());
    }

    @Override
    public CompletableFuture<Void> reverseContinue(final ReverseContinueArguments args) {
        System.out.println("reverseContinue");
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<Void> restartFrame(final RestartFrameArguments args) {
        System.out.println("restartFrame");
        return CompletableFuture.completedFuture(null);
    }

    @Override
    public CompletableFuture<SetExpressionResponse> setExpression(final SetExpressionArguments args) {
        System.out.println("setExpression");
        return CompletableFuture.completedFuture(new SetExpressionResponse());
    }

    @Override
    public CompletableFuture<StepInTargetsResponse> stepInTargets(final StepInTargetsArguments args) {
        System.out.println("stepInTargets");
        return CompletableFuture.completedFuture(new StepInTargetsResponse());
    }

    @Override
    public CompletableFuture<CompletionsResponse> completions(final CompletionsArguments args) {
        System.out.println("completions");
        return CompletableFuture.completedFuture(new CompletionsResponse());
    }

    @Override
    public CompletableFuture<ReadMemoryResponse> readMemory(final ReadMemoryArguments args) {
        System.out.println("readMemory");
        return CompletableFuture.completedFuture(new ReadMemoryResponse());
    }

    @Override
    public CompletableFuture<DisassembleResponse> disassemble(final DisassembleArguments args) {
        System.out.println("disassemble");
        return CompletableFuture.completedFuture(new DisassembleResponse());
    }

    @Override
    public synchronized CompletableFuture<BreakpointLocationsResponse> breakpointLocations(final BreakpointLocationsArguments args) {
        System.out.println("breakpointLocations");
        // https://microsoft.github.io/debug-adapter-protocol/specification#Requests_BreakpointLocations
        // Requires Capabilities#setSupportBreakpointLocationsRequest(true) to be returned in TLCDebugger.initialize(..).
        return CompletableFuture.completedFuture(new BreakpointLocationsResponse());
    }
}
