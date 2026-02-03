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
import java.io.PrintStream;
import java.lang.reflect.Method;

/**
 * Abstract base class for MCP tools that execute TLC.
 * 
 * Provides common functionality for TLC initialization, parameter handling,
 * output capture, and Java option processing with isolated class loading to
 * ensure proper static state isolation between runs.
 */
public abstract class TLCTool extends MCPTool {

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

		// Capture output
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream ps = new PrintStream(baos);
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
