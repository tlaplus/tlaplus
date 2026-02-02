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

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import tla2sany.drivers.SANY;
import util.ToolIO;

/**
 * MCP tool for parsing TLA+ modules using SANY.
 * 
 * Thin adapter that translates MCP JSON input to SANY.SANYmain(String[]) call.
 */
public class SANYParseTool implements MCPTool {

	@Override
	public String getDescription() {
		return "Parse the input TLA+ module using SANY from the TLA+ tools. Use SANY to perform "
				+ "syntax and level-checking of the module. Ensure that the input is provided as a "
				+ "fully qualified file path, as required by the tool.";
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

		// Capture SANY output (redirect ToolIO streams)
		ByteArrayOutputStream baos = new ByteArrayOutputStream();
		PrintStream captureStream = new PrintStream(baos);
		PrintStream oldOut = ToolIO.out;
		PrintStream oldErr = ToolIO.err;

		try {
			ToolIO.out = captureStream;
			ToolIO.err = captureStream;

			// Call SANY main entry point with command-line args
			SANY.SANYmain(new String[] { fileName });

			captureStream.flush();
			String output = baos.toString();

			// Return SANY output directly
			JsonObject result = new JsonObject();
			JsonArray content = new JsonArray();
			JsonObject contentItem = new JsonObject();
			contentItem.addProperty("type", "text");
			contentItem.addProperty("text", output);
			content.add(contentItem);
			result.add("content", content);
			return result;

		} finally {
			ToolIO.out = oldOut;
			ToolIO.err = oldErr;
			captureStream.close();
		}
	}
}
