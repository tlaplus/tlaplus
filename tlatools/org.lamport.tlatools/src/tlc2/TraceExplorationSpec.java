package tlc2;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Date;
import java.util.List;
import java.util.Optional;

import tlc2.input.MCParser;
import tlc2.input.MCParserResults;
import tlc2.model.MCError;
import tlc2.output.EC;
import tlc2.output.ErrorTraceMessagePrinterRecorder;
import tlc2.output.MP;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.impl.ModelConfig;
import tlc2.tool.impl.SpecProcessor;
import util.TLAConstants;

/**
 * Logic for generating a trace exploration (TE) spec.
 */
public class TraceExplorationSpec {
	
	/**
	 * Records TLC output as it runs, capturing the error trace if one is found.
	 */
	private final ErrorTraceMessagePrinterRecorder recorder;
	
	private final Path outputPath;

	private final String originalModuleName;

	private final String teSpecModuleName;
	
	/**
	 * Initializes a new instance of the {@link TraceExplorationSpec} class.
	 * @param output Directory to which to output the TE spec.
	 * @param timestamp Timestamp to include in TE spec filename.
	 * @param recorder Recorder to record TLC as it runs; assumed to already be subscribed.
	 */
	public TraceExplorationSpec(
			Path output,
			Date timestamp,
			String originalModuleName,
			ErrorTraceMessagePrinterRecorder recorder) {
		this.outputPath = output;
		this.teSpecModuleName = deriveTESpecModuleName(originalModuleName, timestamp);
		this.originalModuleName = originalModuleName;
		this.recorder = recorder;
	}
	
	public TraceExplorationSpec(
			Path output,
			String teModuleName,
			String originalModuleName,
			ErrorTraceMessagePrinterRecorder recorder) {
		this.outputPath = output;
		this.teSpecModuleName = teModuleName;
		this.originalModuleName = originalModuleName;
		this.recorder = recorder;
	}
	
	/**
	 * Generates the TE spec and writes it to TLA and CFG files.
	 * @param specInfo Information about the original spec.
	 * @return Either TE spec details or an error message.
	 */
	public Optional<TraceExplorationSpecGenerationReport> generate(ITool specInfo) {
		return this.recorder.getMCErrorTrace().map(errorTrace -> {
			ModelConfig cfg = specInfo.getModelConfig();
			SpecProcessor spec = specInfo.getSpecProcessor();
			List<String> variables = Arrays.asList(TLCState.Empty.getVarsAsStrings());
			MCParserResults parserResults = MCParser.generateResultsFromProcessorAndConfig(spec, cfg);
			return this.generate(parserResults, variables, errorTrace, specInfo);
		});
	}

	/**
	 * Generates the TE spec and writes it to TLA and CFG files.
	 * @param ogModuleName Name of the original spec.
	 * @param constants Constants from the original spec; to be put into cfg file.
	 * 	example value: { "CONSTANT X <- XVal", "CONSTANT Y <- YVAL" }
	 * @param variables Variables from the original spec.
	 * 	example value: { "x", "y" }
	 * @param errorTrace The error trace.
	 */
	private	TraceExplorationSpecGenerationReport generate(
			MCParserResults parserResults,
			List<String> variables,
			MCError errorTrace,
			ITool specInfo) {

		// TODO Handle the case that TLC threw an unexpected exception, which generally
		// translates into EC.General and should be interceptable with a
		// tlc2.output.IMessagePrinterRecorder.
		// If TLC started from a checkpoint (`-recover`), we don't want to generate a TE spec.
		if ((errorTrace.getStates().size() <= 1)
				|| (TLCGlobals.mainChecker != null && TLCGlobals.mainChecker.isRecovery())) {
			return null;
		}

		// Create any intermediate folders if they don't exist.
		this.outputPath.toFile().mkdirs();
		
		final Path teSpecPath = this.outputPath.resolve(teSpecModuleName + TLAConstants.Files.TLA_EXTENSION);
		final Path teConfigPath = this.outputPath.resolve(teSpecModuleName + TLAConstants.Files.CONFIG_EXTENSION);
		try (OutputStream tlaStream = new FileOutputStream(teSpecPath.toFile());
				OutputStream cfgStream = new FileOutputStream(teConfigPath.toFile());) {
			TraceExplorer.writeSpecTEStreams(teSpecModuleName, originalModuleName, parserResults, variables, errorTrace,
					specInfo, tlaStream, cfgStream);
			TraceExplorationSpecGenerationReport report = new TraceExplorationSpecGenerationReport(errorTrace,
					teSpecPath, teConfigPath);
			MP.printMessage(EC.TLC_TE_SPEC_GENERATION_COMPLETE, report.teSpecTlaPath.toString());
			return report;
		} catch (SecurityException | IOException e) {
			MP.printMessage(EC.TLC_TE_SPEC_GENERATION_ERROR, e.getMessage());
		}
		return null;
	}
	
	public static String teModuleId(Date timestamp) {
		final long secondsSinceEpoch = timestamp.getTime() / 1_000L;
		return Long.toString(secondsSinceEpoch);
	}
	
	/**
	 * Derives the TE spec module name.
	 * @param ogModuleName Original module name.
	 * @return The TE spec module name.
	 */
	public static String deriveTESpecModuleName(String ogModuleName, Date timestamp) {
		// millis to secondPaths
		return String.format(
			"%s_%s_%s",
			ogModuleName,
			TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME,
			teModuleId(timestamp));
	}
	
	/**
	 * Determines whether the given spec is a TE spec.
	 * @param tlaFilePath Path to the TLA file.
	 * @return Whether the given spec is a TE spec.
	 */
	public static boolean isTESpecFile(String tlaFilePath) {
		if (null == tlaFilePath) {
			return false;
		}
		
		try {
			// TODO: branch based on something better than the filename such as the module
			// name that we choose above, or check for special tokens/symbols generated in
			// trace spec.
			String filename = Paths.get(tlaFilePath).getFileName().toString();
			// see tlc2.TraceExplorationSpec.deriveTESpecModuleName(String)
			return filename
					.matches("^.*_" + TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + ".*(.tla)?$");
		} catch (InvalidPathException e) { return false; }
	}
}
