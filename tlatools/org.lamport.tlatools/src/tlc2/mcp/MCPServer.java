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

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.google.gson.Gson;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;
import com.google.gson.JsonParser;

/**
 * MCP (Model Context Protocol) server implementation using stdio transport.
 * 
 * This server implements the MCP protocol for TLA+ tools, providing access to
 * SANY parsing, symbol extraction, module listing, and TLC model checking
 * capabilities over JSON-RPC 2.0 via standard input/output.
 * 
 * The server runs in a stateless mode, processing each request independently
 * without maintaining session state between requests.
 * 
 * <h2>Transport Format</h2> This implementation uses newline-delimited JSON
 * over stdio, following the common practice for stdio-based MCP servers. Each
 * JSON-RPC message MUST be:
 * <ul>
 * <li>Serialized as a single line (no embedded newlines)</li>
 * <li>Terminated with a newline character (\n)</li>
 * <li>UTF-8 encoded</li>
 * </ul>
 * 
 * Example valid input:
 * 
 * <pre>
 * {"jsonrpc":"2.0","id":1,"method":"initialize","params":{...}}
 * </pre>
 * 
 * This approach is simpler than Content-Length framing (used by LSP) and is the
 * de-facto standard for stdio-based MCP implementations. See the MCP
 * specification at
 * https://spec.modelcontextprotocol.io/specification/basic/transports/ for
 * details on stdio transport requirements.
 * 
 * <strong>Note:</strong> Pretty-printed JSON with embedded newlines will cause
 * parse errors. Clients must compact JSON to a single line before sending.
 */
public class MCPServer {

	private final BufferedReader reader;
	private final PrintWriter writer;
	private final Gson gson;
	private final Map<String, MCPTool> tools;
	private final KnowledgeBaseResource knowledgeBase;

	/**
	 * Initialize the MCP server with stdio transport.
	 */
	public MCPServer() {
		this.reader = new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
		this.writer = new PrintWriter(new BufferedWriter(new OutputStreamWriter(System.out, StandardCharsets.UTF_8)),
				true);
		// Use compact JSON (no pretty printing) - MCP requires single-line JSON
		// responses
		this.gson = new Gson();
		this.tools = new HashMap<>();
		this.knowledgeBase = new KnowledgeBaseResource();

		// Register all MCP tools
		registerTools();
	}

	/**
	 * Register all available MCP tools.
	 */
	private void registerTools() {
		tools.put("tlaplus_mcp_sany_parse", new SANYParseTool());
		tools.put("tlaplus_mcp_sany_symbol", new SANYSymbolTool());
		tools.put("tlaplus_mcp_sany_modules", new SANYModulesTool());
		tools.put("tlaplus_mcp_tlc_check", new TLCCheckTool());
		tools.put("tlaplus_mcp_tlc_smoke", new TLCSmokeTool());
		tools.put("tlaplus_mcp_tlc_explore", new TLCExploreTool());
		tools.put("tlaplus_mcp_tlc_trace", new TLCTraceTool());
	}

	/**
	 * Start the MCP server and process requests from stdin.
	 * 
	 * Reads newline-delimited JSON-RPC messages from stdin. Each message must be a
	 * complete JSON object on a single line, terminated by \n. Empty lines are
	 * ignored. Responses are written to stdout as single-line JSON followed by \n.
	 * 
	 * The server loops until stdin is closed or an unrecoverable error occurs.
	 */
	public void start() {
		try {
			String line;
			while ((line = reader.readLine()) != null) {
				if (line.trim().isEmpty()) {
					continue;
				}

				try {
					JsonObject request = JsonParser.parseString(line).getAsJsonObject();
					JsonObject response = handleRequest(request);
					writer.println(gson.toJson(response));
				} catch (Exception e) {
					JsonObject errorResponse = createErrorResponse(null, -32700, "Parse error: " + e.getMessage());
					writer.println(gson.toJson(errorResponse));
				}
			}
		} catch (Exception e) {
			System.err.println("Fatal error in MCP server: " + e.getMessage());
			e.printStackTrace(System.err);
		}
	}

	/**
	 * Handle a single JSON-RPC request.
	 */
	private JsonObject handleRequest(JsonObject request) {
		JsonElement idElement = request.get("id");
		String method = request.has("method") ? request.get("method").getAsString() : null;

		if (method == null) {
			return createErrorResponse(idElement, -32600, "Invalid Request: missing method");
		}

		// Handle MCP protocol methods
		switch (method) {
		case "initialize":
			return handleInitialize(idElement, request);
		case "tools/list":
			return handleToolsList(idElement);
		case "tools/call":
			return handleToolCall(idElement, request);
		case "resources/list":
			return handleResourcesList(idElement);
		case "resources/read":
			return handleResourcesRead(idElement, request);
		default:
			return createErrorResponse(idElement, -32601, "Method not found: " + method);
		}
	}

	/**
	 * Handle initialize request.
	 */
	private JsonObject handleInitialize(JsonElement id, JsonObject request) {
		JsonObject result = new JsonObject();
		result.addProperty("protocolVersion", "2024-11-05");

		JsonObject capabilities = new JsonObject();

		// Tools capability
		JsonObject toolsCapability = new JsonObject();
		toolsCapability.addProperty("listChanged", false);
		capabilities.add("tools", toolsCapability);

		// Resources capability
		JsonObject resourcesCapability = new JsonObject();
		resourcesCapability.addProperty("subscribe", false);
		resourcesCapability.addProperty("listChanged", false);
		capabilities.add("resources", resourcesCapability);

		result.add("capabilities", capabilities);

		JsonObject serverInfo = new JsonObject();
		serverInfo.addProperty("name", "TLA+ MCP Tools");
		serverInfo.addProperty("version", "1.0.0");
		result.add("serverInfo", serverInfo);

		return createSuccessResponse(id, result);
	}

	/**
	 * Handle tools/list request.
	 */
	private JsonObject handleToolsList(JsonElement id) {
		JsonObject result = new JsonObject();

		List<JsonObject> toolsList = new ArrayList<>();

		for (Map.Entry<String, MCPTool> entry : tools.entrySet()) {
			MCPTool tool = entry.getValue();
			JsonObject toolDef = new JsonObject();
			toolDef.addProperty("name", entry.getKey());
			toolDef.addProperty("description", tool.getDescription());
			toolDef.add("inputSchema", tool.getInputSchema());
			toolsList.add(toolDef);
		}

		result.add("tools", gson.toJsonTree(toolsList));
		return createSuccessResponse(id, result);
	}

	/**
	 * Handle tools/call request.
	 */
	private JsonObject handleToolCall(JsonElement id, JsonObject request) {
		if (!request.has("params")) {
			return createErrorResponse(id, -32602, "Invalid params: missing params object");
		}

		JsonObject params = request.getAsJsonObject("params");

		if (!params.has("name")) {
			return createErrorResponse(id, -32602, "Invalid params: missing tool name");
		}

		String toolName = params.get("name").getAsString();
		MCPTool tool = tools.get(toolName);

		if (tool == null) {
			return createErrorResponse(id, -32602, "Tool not found: " + toolName);
		}

		JsonObject arguments = params.has("arguments") ? params.getAsJsonObject("arguments") : new JsonObject();

		try {
			JsonObject result = tool.execute(arguments);
			return createSuccessResponse(id, result);
		} catch (Exception e) {
			String errorMsg = "Tool execution failed: " + e.getMessage();
			return createErrorResponse(id, -32000, errorMsg);
		}
	}

	/**
	 * Create a JSON-RPC success response.
	 */
	private JsonObject createSuccessResponse(JsonElement id, JsonObject result) {
		JsonObject response = new JsonObject();
		response.addProperty("jsonrpc", "2.0");
		response.add("id", id);
		response.add("result", result);
		return response;
	}

	/**
	 * Handle resources/list request.
	 */
	private JsonObject handleResourcesList(JsonElement id) {
		try {
			JsonObject result = knowledgeBase.listResources();
			return createSuccessResponse(id, result);
		} catch (Exception e) {
			String errorMsg = "Failed to list resources: " + e.getMessage();
			return createErrorResponse(id, -32000, errorMsg);
		}
	}

	/**
	 * Handle resources/read request.
	 */
	private JsonObject handleResourcesRead(JsonElement id, JsonObject request) {
		if (!request.has("params")) {
			return createErrorResponse(id, -32602, "Invalid params: missing params object");
		}

		JsonObject params = request.getAsJsonObject("params");

		if (!params.has("uri")) {
			return createErrorResponse(id, -32602, "Invalid params: missing uri");
		}

		String uri = params.get("uri").getAsString();

		try {
			JsonObject result = knowledgeBase.readResource(uri);
			return createSuccessResponse(id, result);
		} catch (Exception e) {
			String errorMsg = "Failed to read resource: " + e.getMessage();
			return createErrorResponse(id, -32000, errorMsg);
		}
	}

	/**
	 * Create a JSON-RPC error response.
	 */
	private JsonObject createErrorResponse(JsonElement id, int code, String message) {
		JsonObject response = new JsonObject();
		response.addProperty("jsonrpc", "2.0");
		response.add("id", id);

		JsonObject error = new JsonObject();
		error.addProperty("code", code);
		error.addProperty("message", message);
		response.add("error", error);

		return response;
	}

	/**
	 * Main entry point for running the MCP server.
	 */
	public static void main(String[] args) {
		MCPServer server = new MCPServer();
		server.start();
	}
}
