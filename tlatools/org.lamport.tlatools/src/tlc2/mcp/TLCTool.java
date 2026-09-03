/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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
 *   Markus Alexander Kuppe - initial implementation
 ******************************************************************************/
package tlc2.mcp;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.lang.reflect.Method;
import java.nio.charset.StandardCharsets;

import tlc2.output.MP;

/**
 * Abstract base class for MCP tools that execute TLC.
 * 
 * Provides common functionality for TLC initialization, parameter handling,
 * output capture, and Java option processing with isolated class loading to
 * ensure proper static state isolation between runs.
 */
public abstract class TLCTool extends MCPTool {

	/**
	 * Custom output stream that captures output to a buffer while also streaming
	 * notifications to a callback. When TLC runs in -tool mode, it uses markers
	 * to delimit messages:
	 * - Start: @!@!@STARTMSG <code>:<class> @!@!@
	 * - End: @!@!@ENDMSG <code> @!@!@
	 * 
	 * This class parses these markers and sends complete messages (which may span
	 * multiple lines) as single notifications. The markers themselves are filtered
	 * out from the final output buffer.
	 */
	private static class StreamingOutputStream extends OutputStream {
		private final ByteArrayOutputStream buffer;
		private final NotificationSender notificationSender;
		private final StringBuilder lineBuffer;
		private final StringBuilder cleanLineBuffer;
		private final StringBuilder messageBuffer;
		private boolean insideMessage;
		private static final String START_MARKER = MP.DELIM + MP.STARTMSG;
		private static final String END_MARKER = MP.DELIM + MP.ENDMSG;

		public StreamingOutputStream(ByteArrayOutputStream buffer, NotificationSender notificationSender) {
			this.buffer = buffer;
			this.notificationSender = notificationSender;
			this.lineBuffer = new StringBuilder();
			this.cleanLineBuffer = new StringBuilder();
			this.messageBuffer = new StringBuilder();
			this.insideMessage = false;
		}

		@Override
		public void write(int b) throws IOException {
			// Buffer bytes for line processing
			char c = (char) b;
			if (c == '\n') {
				// Process complete line
				String line = lineBuffer.toString();
				boolean isMarkerLine = processLine(line);
				
				// Only write to output buffer if it's not a marker line
				if (!isMarkerLine) {
					// Write the accumulated clean line
					byte[] lineBytes = cleanLineBuffer.toString().getBytes(StandardCharsets.UTF_8);
					buffer.write(lineBytes);
					buffer.write('\n');
				}
				
				// Always clear buffers after processing a line
				cleanLineBuffer.setLength(0);
				lineBuffer.setLength(0);
			} else if (c != '\r') {
				lineBuffer.append(c);
				cleanLineBuffer.append(c);
			}
		}

		private boolean processLine(String line) {
			if (line.contains(START_MARKER)) {
				// Start of a new TLC message
				insideMessage = true;
				messageBuffer.setLength(0);
				// Don't include the marker line itself
				return true; // This is a marker line
			} else if (line.contains(END_MARKER)) {
				// End of TLC message - send the accumulated message
				if (insideMessage && messageBuffer.length() > 0) {
					String message = messageBuffer.toString().trim();
					if (!message.isEmpty() && notificationSender != null) {
						notificationSender.sendNotification(message);
					}
				}
				insideMessage = false;
				messageBuffer.setLength(0);
				return true; // This is a marker line
			} else if (insideMessage) {
				// Inside a message - accumulate lines
				if (messageBuffer.length() > 0) {
					messageBuffer.append('\n');
				}
				messageBuffer.append(line);
				return false; // Not a marker line
			} else {
				// Outside markers - send individual line as notification
				// (for any output that doesn't use -tool markers)
				if (!line.trim().isEmpty() && notificationSender != null) {
					notificationSender.sendNotification(line);
				}
				return false; // Not a marker line
			}
		}

		@Override
		public void flush() throws IOException {
			// Process any remaining content in line buffer
			if (lineBuffer.length() > 0) {
				String line = lineBuffer.toString();
				boolean isMarkerLine = processLine(line);
				
				// Write to buffer if not a marker line
				if (!isMarkerLine && cleanLineBuffer.length() > 0) {
					byte[] lineBytes = cleanLineBuffer.toString().getBytes(StandardCharsets.UTF_8);
					buffer.write(lineBytes);
				}
				
				// Always clear buffers
				cleanLineBuffer.setLength(0);
				lineBuffer.setLength(0);
			}
			
			// Send any remaining message content
			if (notificationSender != null && messageBuffer.length() > 0) {
				String message = messageBuffer.toString().trim();
				if (!message.isEmpty()) {
					notificationSender.sendNotification(message);
				}
				messageBuffer.setLength(0);
				insideMessage = false;
			}
			
			buffer.flush();
		}
	}

	/**
	 * Execute TLC with the provided arguments and capture its output.
	 * 
	 * This method handles: - Applying Java options from extraJavaOpts - Capturing
	 * stdout/stderr output - Creating an isolated class loader for TLC - Creating
	 * and initializing TLC instance via reflection - Running TLC and collecting
	 * exit code - Restoring output streams - Cleaning up isolated class loader and
	 * MBeans
	 * 
	 * @param tlcArgs       Array of command-line arguments to pass to TLC
	 * @param extraJavaOpts Optional array of Java options to apply (e.g.,
	 *                      ["-Xmx4g", "-Dtlc2.TLC.stopAfter=60"])
	 * @return TLCResult containing exit code and captured output
	 * @throws Exception if TLC parameter parsing or execution fails
	 */
	protected TLCResult executeTLC(String[] tlcArgs, String[] extraJavaOpts) throws Exception {
		return executeTLC(tlcArgs, extraJavaOpts, null);
	}

	/**
	 * Execute TLC with the provided arguments, capture its output, and stream
	 * progress notifications.
	 * 
	 * This method handles: - Applying Java options from extraJavaOpts - Capturing
	 * stdout/stderr output - Streaming output line-by-line as notifications -
	 * Creating an isolated class loader for TLC - Creating and initializing TLC
	 * instance via reflection - Running TLC and collecting exit code - Restoring
	 * output streams - Cleaning up isolated class loader and MBeans
	 * 
	 * @param tlcArgs            Array of command-line arguments to pass to TLC
	 * @param extraJavaOpts      Optional array of Java options to apply (e.g.,
	 *                           ["-Xmx4g", "-Dtlc2.TLC.stopAfter=60"])
	 * @param notificationSender Optional callback for streaming notifications
	 * @return TLCResult containing exit code and captured output
	 * @throws Exception if TLC parameter parsing or execution fails
	 */
	protected TLCResult executeTLC(String[] tlcArgs, String[] extraJavaOpts, NotificationSender notificationSender)
			throws Exception {
		// Apply Java options if provided
		for (String optStr : extraJavaOpts) {
			// Parse Java options like -Dtlc2.TLC.stopAfter=60
			if (optStr.startsWith("-D")) {
				String[] parts = optStr.substring(2).split("=", 2);
				if (parts.length == 2) {
					System.setProperty(parts[0], parts[1]);
				}
			}
		}

		// Create an isolated class loader using base class method
		IsolatedClassLoader isolatedLoader = createIsolatedClassLoader();

		// Capture output with streaming support
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		StreamingOutputStream streamingOut = new StreamingOutputStream(baos, notificationSender);
		PrintStream ps = new PrintStream(streamingOut, true, StandardCharsets.UTF_8);
		PrintStream oldOut = System.out;
		PrintStream oldErr = System.err;

		try {
			System.setOut(ps);
			System.setErr(ps);

			// Load TLC class in the isolated loader
			Class<?> tlcClass = isolatedLoader.loadClass("tlc2.TLC");

			// Create TLC instance
			Object tlcInstance = tlcClass.getDeclaredConstructor().newInstance();

			// Call handleParameters(String[] args)
			Method handleParameters = tlcClass.getMethod("handleParameters", String[].class);
			Object paramResult = handleParameters.invoke(tlcInstance, (Object) tlcArgs);
			if (!(Boolean) paramResult) {
				throw new Exception("Failed to parse TLC parameters");
			}

			// Call process()
			Method process = tlcClass.getMethod("process");
			Object result = process.invoke(tlcInstance);
			int exitCode = (Integer) result;

			ps.flush();
			streamingOut.flush();
			String output = baos.toString();

			return new TLCResult(exitCode, output);

		} finally {
			System.setOut(oldOut);
			System.setErr(oldErr);
			ps.close();

			// Unregister all TLC MBeans to avoid conflicts in subsequent runs
			unregisterTLCMBeans();

			// Clean up class loader
			isolatedLoader.close();
		}
	}

	/**
	 * Container for TLC execution results.
	 */
	protected static class TLCResult {
		public final int exitCode;
		public final String output;

		public TLCResult(int exitCode, String output) {
			this.exitCode = exitCode;
			this.output = output;
		}
	}
}
