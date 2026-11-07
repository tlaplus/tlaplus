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
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.Random;

import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import tlc2.util.FP64;

/**
 * MCP tool for exhaustive model checking with TLC.
 * 
 * Performs exhaustive state-space exploration to verify correctness properties.
 */
public class TLCCheckTool extends TLCTool {

	@Override
	public String getDescription() {
		return "Perform an exhaustive model check of the TLA+ module provided as an input file using TLC. "
				+ "Model checking is a formal verification method that systematically explores all reachable "
				+ "states of a system to verify its correctness. This includes checking both safety and liveness "
				+ "properties, and identifying any counterexamples that violate the specified properties. "
				+ "By default, when a counterexample is found, this tool automatically dumps the error trace to a "
				+ ".tlc file, which can then be replayed using the tlaplus_mcp_tlc_trace tool with custom ALIAS "
				+ "expressions for trace analysis and visualization. "
				+ "Please note that TLC requires the fully qualified file path to the TLA+ module. "
				+ "Be aware that, due to the potential for state-space explosion, exhaustive model checking "
				+ "may be computationally intensive and time-consuming. In some cases, it may be infeasible "
				+ "to check very large models exhaustively.";
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

		JsonObject dumpTrace = new JsonObject();
		dumpTrace.addProperty("type", "boolean");
		dumpTrace.addProperty("description",
				"Whether to automatically dump counterexample traces to a .tlc file. "
						+ "Defaults to true. The trace file can then be loaded with tlaplus_mcp_tlc_trace tool. "
						+ "If a counterexample is found, a trace file will be created with the naming pattern: "
						+ "{specName}_trace_T{timestamp}_F{fp}_W{workers}_Mmodelcheck.tlc");
		properties.add("dumpTrace", dumpTrace);

		JsonObject traceFile = new JsonObject();
		traceFile.addProperty("type", "string");
		traceFile.addProperty("description",
				"Optional custom path for the trace file. If not provided, a trace file will be "
						+ "automatically generated in the same directory as the spec file when dumpTrace is enabled.");
		properties.add("traceFile", traceFile);

		JsonObject extraOpts = new JsonObject();
		extraOpts.addProperty("type", "array");
		JsonObject extraOptsItems = new JsonObject();
		extraOptsItems.addProperty("type", "string");
		extraOpts.add("items", extraOptsItems);
		extraOpts.addProperty("description",
				"Optional array of additional command-line options to pass to TLC beyond [-modelcheck].");
		properties.add("extraOpts", extraOpts);

		JsonObject extraJavaOpts = new JsonObject();
		extraJavaOpts.addProperty("type", "array");
		JsonObject extraJavaOptsItems = new JsonObject();
		extraJavaOptsItems.addProperty("type", "string");
		extraJavaOpts.add("items", extraJavaOptsItems);
		extraJavaOpts.addProperty("description",
				"Optional array of additional Java options to pass to the JVM (e.g., [\"-Xmx4g\", \"-Dtlc2.TLC.stopAfter=60\"]).");
		properties.add("extraJavaOpts", extraJavaOpts);

		schema.add("properties", properties);

		JsonArray required = new JsonArray();
		required.add("fileName");
		schema.add("required", required);

		return schema;
	}

	/**
	 * Generate a trace filename following the pattern:
	 * {specName}_trace_T{timestamp}_F{fp}_W{workers}_M{mode}.tlc
	 * 
	 * @param specFile    The spec file path
	 * @param fingerprint The fingerprint value (must not be null)
	 * @param workers     Number of workers or "auto" (must not be null)
	 * @param mode        The mode (e.g., "modelcheck")
	 * @return The generated trace filename
	 */
	private String generateTraceFilename(String specFile, int fingerprint, String workers, String mode) {
		File file = new File(specFile);
		String specName = file.getName();
		// Remove .tla extension if present
		if (specName.endsWith(".tla")) {
			specName = specName.substring(0, specName.length() - 4);
		}

		// Format timestamp
		SimpleDateFormat sdf = new SimpleDateFormat("yyyy-MM-dd_HH-mm-ss");
		String timestamp = sdf.format(new Date());

		// Build filename
		StringBuilder filename = new StringBuilder();
		filename.append(specName);
		filename.append("_trace_T").append(timestamp);
		filename.append("_F").append(fingerprint);
		filename.append("_W").append(workers);
		filename.append("_M").append(mode);
		filename.append(".tlc");

		// Use the same directory as the spec file
		String parentDir = file.getParent();
		if (parentDir != null) {
			return new File(parentDir, filename.toString()).getAbsolutePath();
		} else {
			return filename.toString();
		}
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

		// Check if trace dumping is enabled (default: true)
		boolean dumpTrace = true;
		if (arguments.has("dumpTrace")) {
			dumpTrace = arguments.get("dumpTrace").getAsBoolean();
		}

		// Extract fingerprint and workers for trace filename generation
		Integer fingerprint = null;
		String workers = null;

		// Build TLC arguments
		List<String> tlcArgs = new ArrayList<>();
		tlcArgs.add("-cleanup");
		tlcArgs.add("-tool");
		tlcArgs.add("-modelcheck");

		// Add extra options and extract fingerprint/workers if present
		if (arguments.has("extraOpts")) {
			JsonArray extraOpts = arguments.getAsJsonArray("extraOpts");
			for (int i = 0; i < extraOpts.size(); i++) {
				String opt = extraOpts.get(i).getAsString();
				tlcArgs.add(opt);

				// Extract fingerprint if specified
				if ("-fp".equalsIgnoreCase(opt) && i + 1 < extraOpts.size()) {
					try {
						fingerprint = Integer.parseInt(extraOpts.get(i + 1).getAsString());
					} catch (NumberFormatException e) {
						// Ignore if not a valid number
					}
				}

				// Extract workers if specified (can be a number or "auto")
				if ("-workers".equalsIgnoreCase(opt) && i + 1 < extraOpts.size()) {
					workers = extraOpts.get(i + 1).getAsString();
				}
			}
		}

		// Add trace dumping if enabled
		String traceFilePath = null;
		if (dumpTrace) {
			// Add -fp option if not already present (required for trace to load correctly)
			// If fingerprint is null, it means -fp was not provided in extraOpts
			if (fingerprint == null) {
				// Randomly choose a fingerprint polynomial
				fingerprint = new Random().nextInt(FP64.Polys.length);
				tlcArgs.add("-fp");
				tlcArgs.add(String.valueOf(fingerprint));
			}

			// Set default for workers if not specified
			if (workers == null) {
				workers = "1";
			}

			if (arguments.has("traceFile")) {
				traceFilePath = arguments.get("traceFile").getAsString();
			} else {
				// Auto-generate trace filename
				traceFilePath = generateTraceFilename(fileName, fingerprint, workers, "bfs");
			}

			tlcArgs.add("-dumpTrace");
			tlcArgs.add("tlc");
			tlcArgs.add(traceFilePath);
			
			tlcArgs.add("-noGenerateSpecTE");
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

		// Build result message
		StringBuilder message = new StringBuilder();
		message.append("TLC model checking completed with exit code ").append(result.exitCode);
		message.append(":\n\n").append(result.output);

		JsonObject jsonResult = new JsonObject();
		JsonArray content = new JsonArray();
		JsonObject contentItem = new JsonObject();
		contentItem.addProperty("type", "text");
		contentItem.addProperty("text", message.toString());
		content.add(contentItem);
		jsonResult.add("content", content);

		// Add trace file path to result metadata if available
		if (dumpTrace && traceFilePath != null) {
			jsonResult.addProperty("traceFile", traceFilePath);
		}

		return jsonResult;
	}
}
