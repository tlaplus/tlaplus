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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

/**
 * MCP tool for listing available TLA+ modules.
 * 
 * Retrieves a list of all TLA+ modules that can be imported into a
 * specification.
 */
public class SANYModulesTool implements MCPTool {

	@Override
	public String getDescription() {
		return "Retrieves a list of all TLA+ modules recognized by SANY, making it easy to see "
				+ "which modules can be imported into a TLA+ specification.";
	}

	@Override
	public JsonObject getInputSchema() {
		JsonObject schema = new JsonObject();
		schema.addProperty("type", "object");
		schema.add("properties", new JsonObject());
		return schema;
	}

	@Override
	public JsonObject execute(JsonObject arguments) throws Exception {
		Map<String, List<String>> modulesByPath = new HashMap<>();

		// Get TLA library path from environment
		String tlaLibraryPath = System.getenv("TLA_LIBRARY_PATH");

		List<String> searchPaths = new ArrayList<>();

		// Add current directory
		searchPaths.add(".");

		// Add standard library paths if available
		if (tlaLibraryPath != null && !tlaLibraryPath.isEmpty()) {
			String[] paths = tlaLibraryPath.split(File.pathSeparator);
			for (String path : paths) {
				searchPaths.add(path);
			}
		}

		// Check for standard TLA+ library locations
		String userHome = System.getProperty("user.home");
		if (userHome != null) {
			String[] standardPaths = { userHome + "/.tlaplus", userHome + "/tlaplus", "/usr/share/tlaplus",
					"/usr/local/share/tlaplus" };
			for (String path : standardPaths) {
				File dir = new File(path);
				if (dir.exists() && dir.isDirectory()) {
					searchPaths.add(path);
				}
			}
		}

		// Search each path for .tla files
		for (String searchPath : searchPaths) {
			File dir = new File(searchPath);
			if (dir.exists() && dir.isDirectory()) {
				File[] files = dir.listFiles((d, name) -> name.endsWith(".tla"));
				if (files != null && files.length > 0) {
					List<String> modules = new ArrayList<>();
					for (File file : files) {
						String moduleName = file.getName();
						// Skip modules whose name starts with '_'
						if (!moduleName.startsWith("_")) {
							modules.add(searchPath + File.separator + moduleName);
						}
					}
					if (!modules.isEmpty()) {
						modulesByPath.put(searchPath, modules);
					}
				}
			}
		}

		// Format output
		StringBuilder output = new StringBuilder();
		output.append("Available TLA+ modules from configured search paths:\n\n");

		for (Map.Entry<String, List<String>> entry : modulesByPath.entrySet()) {
			output.append("Search path: ").append(entry.getKey()).append("\n");
			for (String module : entry.getValue()) {
				output.append("  ").append(module).append("\n");
			}
			output.append("\n");
		}

		JsonObject result = new JsonObject();
		JsonArray content = new JsonArray();
		JsonObject contentItem = new JsonObject();
		contentItem.addProperty("type", "text");
		contentItem.addProperty("text", output.toString());
		content.add(contentItem);
		result.add("content", content);
		return result;
	}
}
