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
 * MCP tool for exploring TLA+ specifications by generating random behaviors.
 * 
 * Generates and prints a sequence of states to understand system behavior.
 */
public class TLCExploreTool extends TLCTool {

	@Override
	public String getDescription() {
		return "Explore the given TLA+ module by using TLC to randomly generate and print a behavior—a "
				+ "sequence of states, where each state represents an assignment of values to the module's "
				+ "variables. Choose a meaningful value for the behavior length N that is neither too small "
				+ "nor too large, based on your estimate of what constitutes an interesting behavior for "
				+ "this particular module.";
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

		JsonObject behaviorLength = new JsonObject();
		behaviorLength.addProperty("type", "integer");
		behaviorLength.addProperty("minimum", 1);
		behaviorLength.addProperty("description", "The length of the behavior to generate.");
		properties.add("behaviorLength", behaviorLength);

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
				"Optional array of additional command-line options to pass to TLC beyond [-simulate, -invlevel].");
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
		required.add("behaviorLength");
		schema.add("required", required);

		return schema;
	}

	@Override
	public JsonObject execute(JsonObject arguments, NotificationSender notificationSender) throws Exception {
		if (!arguments.has("fileName")) {
			throw new IllegalArgumentException("Missing required argument: fileName");
		}

		if (!arguments.has("behaviorLength")) {
			throw new IllegalArgumentException("Missing required argument: behaviorLength");
		}

		String fileName = arguments.get("fileName").getAsString();
		int behaviorLength = arguments.get("behaviorLength").getAsInt();

		if (behaviorLength < 1) {
			throw new IllegalArgumentException("behaviorLength must be at least 1");
		}

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

		// Set default stopAfter for exploration
		System.setProperty("tlc2.TLC.stopAfter", "3");

		// Build TLC arguments
		List<String> tlcArgs = new ArrayList<>();
		tlcArgs.add("-cleanup");
		tlcArgs.add("-tool");
		tlcArgs.add("-simulate");
		tlcArgs.add("-invlevel");
		tlcArgs.add(String.valueOf(behaviorLength));

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
		contentItem.addProperty("text", "TLC exploration completed with exit code " + result.exitCode + ":\n\n" + result.output);
		content.add(contentItem);
		jsonResult.add("content", content);
		return jsonResult;
	}
}
