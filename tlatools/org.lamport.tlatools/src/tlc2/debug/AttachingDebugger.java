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

import tlc2.TLCGlobals;
import util.ToolIO;

public class AttachingDebugger extends TLCDebugger {

	public AttachingDebugger() throws IOException, InterruptedException, ExecutionException {
		// Expanding values causes them to be un-lazied/enumerated, which we don't want
		// as a side-effect of the debugger.
		TLCGlobals.expand = false;
		
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
				if (launcher != null) {
					launcher.getRemoteProxy().output(oea);
				}
			}
		};

		Executors.newSingleThreadExecutor().submit(() -> {
			try (ServerSocket serverSocket = new ServerSocket(4712)) {
				// Immediately re-open the debugger to front-end requests after a front-end disconnected.
				//TODO: This doesn't terminate when TLC terminates.
				while (true) {
					System.out.printf("Debugger is listening on %s\n", serverSocket.getLocalSocketAddress());
					final Socket socket = serverSocket.accept();
					final InputStream inputStream = socket.getInputStream();
					final OutputStream outputStream = socket.getOutputStream();

					launcher = DSPLauncher.createServerLauncher(this, inputStream, outputStream);
					launcher.startListening().get(); // This blocks until the front-end disconnects.
				}
			}
		});
	}

	@Override
	public CompletableFuture<Void> launch(Map<String, Object> args) {
		LOGGER.finer("launch");
		Executors.newSingleThreadExecutor().submit(() -> {
			StoppedEventArguments eventArguments = new StoppedEventArguments();
			eventArguments.setThreadId(0);
			launcher.getRemoteProxy().stopped(eventArguments);
		});
		
		return CompletableFuture.completedFuture(null);
	}

	@Override
	protected void sendStopped() {
		LOGGER.finer("loadSource -> stopped");
		if (launcher != null) {
			StoppedEventArguments eventArguments = new StoppedEventArguments();
			eventArguments.setThreadId(0);
			launcher.getRemoteProxy().stopped(eventArguments);
		} else {
			System.out.printf("Debugger has halted TLC and is waiting for the DAP front-end to connect...\n");
		}
	}
}
