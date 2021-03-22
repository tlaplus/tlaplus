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
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;

import org.eclipse.lsp4j.debug.OutputEventArguments;
import org.eclipse.lsp4j.debug.StoppedEventArguments;
import org.eclipse.lsp4j.debug.launch.DSPLauncher;

import util.ToolIO;

public class AttachingDebugger extends TLCDebugger {
	
	private String buffer = "";
	
	public AttachingDebugger(final Step s, final boolean halt) throws IOException, InterruptedException, ExecutionException {
		super(s, halt);
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
					oea.setOutput(str);
					launcher.getRemoteProxy().output(oea);
				} else {
					buffer += str;
				}
			}
		};
	}

	@Override
	public TLCDebugger listen(final int port) {
		Executors.newSingleThreadExecutor().submit(() -> {
			try (ServerSocket serverSocket = new ServerSocket(port)) {
				// Immediately re-open the debugger to front-end requests after a front-end disconnected.
				//TODO: This doesn't terminate when TLC terminates.
				while (true) {
					// No point printing the debugger port while it's hard-coded.
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
