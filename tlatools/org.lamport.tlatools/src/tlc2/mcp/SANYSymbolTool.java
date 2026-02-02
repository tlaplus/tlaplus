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
import java.util.ArrayList;
import java.util.List;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

/**
 * MCP tool for extracting symbols from TLA+ modules.
 * 
 * Thin adapter that translates MCP JSON input to XMLExporter call. The XML
 * output contains all symbol information (constants, variables, operators,
 * etc.)
 */
public class SANYSymbolTool implements MCPTool {

	@Override
	public String getDescription() {
		return "Extract all symbols from the given TLA+ module. Use this tool to identify the symbols "
				+ "defined in a TLA+ specification—such as when generating a TLC configuration file. "
				+ "It assists in determining the list of CONSTANTS, the initialization predicate, the "
				+ "next-state relation, the overall behavior specification (Spec), and any defined safety "
				+ "or liveness properties. Note: SANY expects the fully qualified file path to the TLA+ module.";
	}

	@Override
	public JsonObject getInputSchema() {
		JsonObject schema = new JsonObject();
		schema.addProperty("type", "object");

		JsonObject properties = new JsonObject();

		JsonObject fileName = new JsonObject();
		fileName.addProperty("type", "string");
		fileName.addProperty("description", "The full path to the file containing the TLA+ module.");
		properties.add("fileName", fileName);

		JsonObject includeExtended = new JsonObject();
		includeExtended.addProperty("type", "boolean");
		includeExtended.addProperty("description", "If true, includes symbols from extended and instantiated modules. "
				+ "By default (false), only symbols from the current module are included.");
		properties.add("includeExtendedModules", includeExtended);

		schema.add("properties", properties);

		JsonArray required = new JsonArray();
		required.add("fileName");
		schema.add("required", required);

		return schema;
	}

	@Override
	public JsonObject execute(JsonObject arguments) throws Exception {
		if (!arguments.has("fileName")) {
			throw new IllegalArgumentException("Missing required argument: fileName");
		}

		String fileName = arguments.get("fileName").getAsString();
		boolean includeExtended = arguments.has("includeExtendedModules")
				&& arguments.get("includeExtendedModules").getAsBoolean();

		// Check if file exists
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

		// Build XMLExporter arguments
		List<String> args = new ArrayList<>();

		// Add -r flag for restricted mode (only current module) if not including
		// extended modules
		if (!includeExtended) {
			args.add("-r");
		}

		// Add the filename
		args.add(fileName);

		// Capture XMLExporter output
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream oldOut = System.out;
		PrintStream captureStream = new PrintStream(baos);

		try {
			System.setOut(captureStream);

			// Call XMLExporter
			int exitCode = tla2sany.xml.XMLExporter.run(args.toArray(new String[0]));

			captureStream.flush();
			String xmlOutput = baos.toString();

			// Return XML output
			JsonObject result = new JsonObject();
			JsonArray content = new JsonArray();
			JsonObject contentItem = new JsonObject();
			contentItem.addProperty("type", "text");

			if (exitCode == 0) {
				contentItem.addProperty("text", "Symbol extraction successful:\n" + xmlOutput);
			} else {
				contentItem.addProperty("text", "Symbol extraction failed (exit code " + exitCode + "):\n" + xmlOutput);
			}

			content.add(contentItem);
			result.add("content", content);
			return result;

		} finally {
			System.setOut(oldOut);
			captureStream.close();
		}
	}
}
