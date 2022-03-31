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
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.io.PrintStream;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;

import org.eclipse.lsp4j.debug.OutputEventArguments;
import org.eclipse.lsp4j.debug.StoppedEventArguments;
import org.eclipse.lsp4j.debug.launch.DSPLauncher;

import tlc2.tool.impl.Tool;
import util.ToolIO;

public class AttachingDebugger extends TLCDebugger {
	
	private String buffer = "";
	private final int port;
	
	public AttachingDebugger(int port, final Step s, final boolean halt) throws IOException, InterruptedException, ExecutionException {
		super(s, halt);
		this.port = port;
		
		// Connect TLC's stdin to the debugger's console for users to be able to control
		// TLC should it accept user input on stdin.  For example, a Java module override
		// might prompt a user to respond on stdin.
		final PipedInputStream pin = new PipedInputStream();
		System.setIn(pin);
		pipedOutputStream = new PipedOutputStream(pin);
		
		// Listen to that SANY and TLC have to say, and what gets written with TLC!Print*.
		ToolIO.out = new PrintStream(ToolIO.out) {
			// ToolIO.out passed to PrintStream above is either System.out or one of TLC's
			// ToolIO.ToolPrintStream, TestPrintStream, ..., which intercept print*
			// invocations to store the string parameter.  This instance of a PrintStream
			// is just a wrapper that -in turn- intercept the only two print methods that 
			// TLC invokes.  We cannot simply call super.print* below, because PrintStream
			// delegates those call to out.write instead of out.print.  In other words,
			// ToolIO.ToolPrintStream, TestPrintStream, ..., would not be able to store
			// the string parameters, which causes several tests to fail.
			@Override
			public void println(String str) {
				((PrintStream) out).println(str);
				sendOutput(str + "\n");
			}

			@Override
			public void print(String str) {
				((PrintStream) out).print(str);
				sendOutput(str);
			}

			private void sendOutput(String str) {
				if (launcher != null) {
					final OutputEventArguments oea = new OutputEventArguments();
					// TODO Make use of OutputEventArgumentsCategory and OutputEventArgumentsGroup
					// to make TLC's more readable in a debugger.  For example, TLC's progress
					// messages tend to get mixed up with other, more relevant output.
					// Don't parse the strings here!!! Instead, BroadcastMessagePrinterRecorder
					// provides first-class access to the log output without parsing.
					// When launched from the debugger (VScode), TLC does not run in -tool mode.
					//oea.setGroup(OutputEventArgumentsGroup.START_COLLAPSED);
					//oea.setCategory("Progress");
					oea.setOutput(str);
					launcher.getRemoteProxy().output(oea);
				} else {
					buffer += str;
				}
			}
		};
	}


	@Override
	public IDebugTarget setTool(final Tool tool) {
		super.setTool(tool);
		Executors.newSingleThreadExecutor().submit(() -> {
			try (ServerSocket serverSocket = new ServerSocket(port)) {
				// Immediately re-open the debugger to front-end requests after a front-end disconnected.
				//TODO: This doesn't terminate when TLC terminates.
				while (true) {
					// Beware: Do not remove "Debugger is listening on %s\n" below, because the
					// debugger front-end of the VSCode extension waits for TLC to print this
					// message when connecting to the TLA+ debugger:
					// https://github.com/alygin/vscode-tlaplus/commit/74d4a34cf9e2b3864f7ee51402d88fc3b9f7525f#commitcomment-51478347
					System.out.printf("Debugger is listening on %s\n", serverSocket.getLocalSocketAddress());
					final Socket socket = serverSocket.accept();
					final InputStream inputStream = socket.getInputStream();
					final OutputStream outputStream = socket.getOutputStream();

					launcher = DSPLauncher.createServerLauncher(this, inputStream, outputStream);
					launcher.startListening().get(); // This blocks until the front-end disconnects.
				}
			}
		});
		return this;
	}

	@Override
	public CompletableFuture<Void> launch(Map<String, Object> args) {
		LOGGER.finer("launch");
		Executors.newSingleThreadExecutor().submit(() -> {
			if (!"".equals(buffer)) {
				// Send buffered TLC output that was printed before the debugger connected.
				final OutputEventArguments oea = new OutputEventArguments();
				oea.setOutput(buffer);
				launcher.getRemoteProxy().output(oea);
				buffer = "";
			}
			
			StoppedEventArguments eventArguments = new StoppedEventArguments();
			eventArguments.setThreadId(0);
			launcher.getRemoteProxy().stopped(eventArguments);
		});
		
		return CompletableFuture.completedFuture(null);
	}
}
