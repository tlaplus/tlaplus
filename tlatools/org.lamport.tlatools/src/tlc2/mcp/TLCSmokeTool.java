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

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

/**
 * MCP tool for smoke testing TLA+ specifications using TLC simulation mode.
 * 
 * Runs lightweight verification by randomly exploring behaviors within a time
 * limit.
 */
public class TLCSmokeTool extends TLCTool {

	@Override
	public String getDescription() {
		return "Smoke test the TLA+ module using TLC with the provided input file. Smoke testing is a "
				+ "lightweight verification technique that runs TLC in simulation mode to randomly explore "
				+ "as many behaviors as possible within a specified time limit. This method does not attempt "
				+ "to exhaustively explore the entire state space. If no counterexample is found, it does not "
				+ "imply that the module is correct—only that no violations were observed within the constraints "
				+ "of the test. If a counterexample is found, it demonstrates that the module violates at least "
				+ "one of its specified properties. Note that any counterexample produced may not be minimal "
				+ "due to the non-exhaustive nature of the search. TLC expects the fully qualified file path "
				+ "to the input module.";
	}

	@Override
	public JsonObject getInputSchema() {
		JsonObject schema = new JsonObject();
		schema.addProperty("type", "object");

		JsonObject properties = new JsonObject();

		JsonObject fileName = new JsonObject();
		fileName.addProperty("type", "string");
		fileName.addProperty("description", "The full path to the file containing the TLA+ module to parse.");
		properties.add("fileName", fileName);

		JsonObject cfgFile = new JsonObject();
		cfgFile.addProperty("type", "string");
		cfgFile.addProperty("description", "Optional path to a custom TLC configuration file.");
		properties.add("cfgFile", cfgFile);

		JsonObject extraOpts = new JsonObject();
		extraOpts.addProperty("type", "array");
		JsonObject extraOptsItems = new JsonObject();
		extraOptsItems.addProperty("type", "string");
		extraOpts.add("items", extraOptsItems);
		extraOpts.addProperty("description",
				"Optional array of additional command-line options to pass to TLC beyond [-simulate].");
		properties.add("extraOpts", extraOpts);

		JsonObject extraJavaOpts = new JsonObject();
		extraJavaOpts.addProperty("type", "array");
		JsonObject extraJavaOptsItems = new JsonObject();
		extraJavaOptsItems.addProperty("type", "string");
		extraJavaOpts.add("items", extraJavaOptsItems);
		extraJavaOpts.addProperty("description",
				"Optional array of additional Java options to pass to the JVM (e.g., [\"-Xmx4g\"]). "
						+ "Note: -Dtlc2.TLC.stopAfter=3 is set by default.");
		properties.add("extraJavaOpts", extraJavaOpts);

		schema.add("properties", properties);

		JsonArray required = new JsonArray();
		required.add("fileName");
		schema.add("required", required);

		return schema;
	}

	@Override
	public JsonObject execute(JsonObject arguments, NotificationSender notificationSender) throws Exception {
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

		// Set default stopAfter for smoke testing
		System.setProperty("tlc2.TLC.stopAfter", "3");

		// Build TLC arguments
		List<String> tlcArgs = new ArrayList<>();
		tlcArgs.add("-cleanup");
		tlcArgs.add("-tool");
		tlcArgs.add("-simulate");

		// Add extra options
		if (arguments.has("extraOpts")) {
			JsonArray extraOpts = arguments.getAsJsonArray("extraOpts");
			for (JsonElement opt : extraOpts) {
				tlcArgs.add(opt.getAsString());
			}
		}

		// Add config file if provided
		if (arguments.has("cfgFile")) {
			String cfgFile = arguments.get("cfgFile").getAsString();
			tlcArgs.add("-config");
			tlcArgs.add(cfgFile);
		}

		// Add the spec file
		tlcArgs.add(fileName);

		// Extract Java options if provided
		String[] extraJavaOpts = new String[0];
		if (arguments.has("extraJavaOpts")) {
			JsonArray javaOptsArray = arguments.getAsJsonArray("extraJavaOpts");
			extraJavaOpts = new String[javaOptsArray.size()];
			for (int i = 0; i < javaOptsArray.size(); i++) {
				extraJavaOpts[i] = javaOptsArray.get(i).getAsString();
			}
		}

		// Execute TLC using base class method with streaming support
		TLCResult result = executeTLC(tlcArgs.toArray(new String[0]), extraJavaOpts, notificationSender);

		JsonObject jsonResult = new JsonObject();
		JsonArray content = new JsonArray();
		JsonObject contentItem = new JsonObject();
		contentItem.addProperty("type", "text");
		contentItem.addProperty("text", "TLC smoke test completed with exit code " + result.exitCode + ":\n\n" + result.output);
		content.add(contentItem);
		jsonResult.add("content", content);
		return jsonResult;
	}
}
