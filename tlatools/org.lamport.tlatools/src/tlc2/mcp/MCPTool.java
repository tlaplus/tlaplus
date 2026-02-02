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

import com.google.gson.JsonObject;

/**
 * Interface for MCP tools.
 * 
 * Each tool implementation provides: - A description of what the tool does - An
 * input schema (JSON Schema) defining expected parameters - An execute method
 * that performs the tool's operation
 */
public interface MCPTool {

	/**
	 * Get the human-readable description of this tool.
	 * 
	 * @return Tool description
	 */
	String getDescription();

	/**
	 * Get the JSON Schema for this tool's input parameters.
	 * 
	 * @return JSON Schema object describing the input parameters
	 */
	JsonObject getInputSchema();

	/**
	 * Execute the tool with the given arguments.
	 * 
	 * @param arguments JSON object containing the tool's input parameters
	 * @return JSON object containing the tool's result
	 * @throws Exception if tool execution fails
	 */
	JsonObject execute(JsonObject arguments) throws Exception;
}
