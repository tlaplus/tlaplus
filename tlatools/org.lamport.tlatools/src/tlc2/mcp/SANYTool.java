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
import java.io.File;
import java.io.PrintStream;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

/**
 * Abstract base class for MCP tools that execute SANY or related tools.
 * 
 * Provides common functionality for output capture (both ToolIO and
 * System.out), file existence checking, JSON response building, and isolated
 * class loading to ensure proper static state isolation between runs.
 */
public abstract class SANYTool extends MCPTool {

	/**
	 * Check if a file exists and return an error response if it doesn't.
	 * 
	 * @param fileName The path to the file to check
	 * @return A JsonObject error response if the file doesn't exist, null otherwise
	 */
	protected JsonObject checkFileExists(String fileName) {
		File file = new File(fileName);
		if (!file.exists()) {
			JsonObject result = new JsonObject();
			JsonArray content = new JsonArray();
			JsonObject contentItem = new JsonObject();
			contentItem.addProperty("type", "text");
			contentItem.addProperty("text", "File " + fileName + " does not exist on disk.");
			content.add(contentItem);
			result.add("content", content);
			return result;
		}
		return null;
	}

	/**
	 * Execute SANY with the provided arguments and capture its output.
	 * 
	 * SANY uses ToolIO streams for output, so this method redirects ToolIO.out and
	 * ToolIO.err using an isolated class loader to ensure static state isolation.
	 * 
	 * @param args Array of command-line arguments to pass to SANY
	 * @return Captured output from SANY
	 * @throws Exception if SANY execution fails
	 */
	protected String executeSANY(String[] args) throws Exception {
		// Create an isolated class loader using base class method
		IsolatedClassLoader isolatedLoader = createIsolatedClassLoader();

		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream captureStream = new PrintStream(baos);

		try {
			// Load ToolIO class in the isolated loader
			Class<?> toolIOClass = isolatedLoader.loadClass("util.ToolIO");

			// Get the current ToolIO.out and ToolIO.err via reflection
			Field outField = toolIOClass.getField("out");
			Field errField = toolIOClass.getField("err");

			Object oldOut = outField.get(null);
			Object oldErr = errField.get(null);

			try {
				// Set ToolIO.out and ToolIO.err to capture stream
				outField.set(null, captureStream);
				errField.set(null, captureStream);

				// Load SANY class and invoke SANYmain
				Class<?> sanyClass = isolatedLoader.loadClass("tla2sany.drivers.SANY");
				Method sanyMain = sanyClass.getMethod("SANYmain0", String[].class);
				try {
					sanyMain.invoke(null, (Object) args);
				} catch (InvocationTargetException e) {
					// Unwrap the exception thrown by the invoked method
					Throwable cause = e.getCause();

					// Check if the cause is a SANYExitException
					if (cause != null && "tla2sany.drivers.SANYExitException".equals(cause.getClass().getName())) {
						// SANYExitException indicates SANY exited with an error code
						// The error details are already captured in the output stream
						// We don't re-throw here as we want to return the captured output
						captureStream.flush();
						return baos.toString();
					}

					// For other exceptions, preserve and rethrow the original exception
					cause.printStackTrace(captureStream);
					captureStream.flush();

					// Rethrow based on the exception type to preserve it
					if (cause instanceof Exception) {
						throw (Exception) cause;
					} else if (cause instanceof Error) {
						throw (Error) cause;
					} else {
						// Shouldn't happen, but handle it anyway
						throw new Exception("SANY execution failed with unexpected throwable", cause);
					}
				}

				captureStream.flush();
				return baos.toString();

			} finally {
				// Restore ToolIO streams
				outField.set(null, oldOut);
				errField.set(null, oldErr);
				captureStream.close();
			}

		} finally {
			// Unregister all TLC MBeans to avoid conflicts in subsequent runs
			unregisterTLCMBeans();

			// Clean up class loader
			isolatedLoader.close();
		}
	}

	/**
	 * Execute XMLExporter with the provided arguments and capture its output.
	 * 
	 * XMLExporter uses System.out for output, so this method redirects System.out
	 * using an isolated class loader to ensure static state isolation.
	 * 
	 * @param args Array of command-line arguments to pass to XMLExporter
	 * @return Captured output from XMLExporter
	 * @throws Exception if XMLExporter execution fails
	 */
	protected String executeXMLExporter(String[] args) throws Exception {
		// Create an isolated class loader using base class method
		IsolatedClassLoader isolatedLoader = createIsolatedClassLoader();

		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream captureStream = new PrintStream(baos);
		PrintStream oldOut = System.out;

		try {
			System.setOut(captureStream);

			// Load XMLExporter class and invoke run method
			Class<?> xmlExporterClass = isolatedLoader.loadClass("tla2sany.xml.XMLExporter");
			Method runMethod = xmlExporterClass.getMethod("run", String[].class);
			runMethod.invoke(null, (Object) args);

			captureStream.flush();
			return baos.toString();

		} finally {
			System.setOut(oldOut);
			captureStream.close();

			// Unregister all TLC MBeans to avoid conflicts in subsequent runs
			unregisterTLCMBeans();

			// Clean up class loader
			isolatedLoader.close();
		}
	}

	/**
	 * Build a standard JSON response with text content.
	 * 
	 * @param text The text content to include in the response
	 * @return JsonObject containing the formatted response
	 */
	protected JsonObject buildTextResponse(String text) {
		JsonObject result = new JsonObject();
		JsonArray content = new JsonArray();
		JsonObject contentItem = new JsonObject();
		contentItem.addProperty("type", "text");
		contentItem.addProperty("text", text);
		content.add(contentItem);
		result.add("content", content);
		return result;
	}
}
