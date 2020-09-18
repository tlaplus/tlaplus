package tlc2;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

import tlc2.input.MCParser;
import tlc2.input.MCParserResults;
import tlc2.model.MCError;
import tlc2.output.MP;
import tlc2.output.EC;
import tlc2.output.ErrorTraceMessagePrinterRecorder;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.impl.ModelConfig;
import tlc2.tool.impl.SpecProcessor;
import util.TLAConstants;

/**
 * Logic for generating a trace expression (TE) spec.
 */
public class TraceExpressionSpec {
	
	/**
	 * Directory to which TE spec is written.
	 */
	private Path outputDirectory = null;
	
	/**
	 * Resolves TE spec files & provides output streams to them.
	 */
	private IStreamProvider streamProvider;
	
	/**
	 * Records TLC output as it runs, capturing the error trace if one is found.
	 */
	private ErrorTraceMessagePrinterRecorder recorder;
	
	/**
	 * Initializes a new instance of the {@link TraceExpressionSpec} class.
	 * @param outputDirectory Directory to which to output the TE spec.
	 * @param recorder Recorder to record TLC as it runs; assumed to already be subscribed.
	 */
	public TraceExpressionSpec(
			Path outputDirectory,
			ErrorTraceMessagePrinterRecorder recorder) {
		this.outputDirectory = outputDirectory;
		this.streamProvider = new FileStreamProvider(outputDirectory);
		this.recorder = recorder;
	}
	
	/**
	 * Initializes a new instance of the {@link TraceExpressionSpec} class.
	 * This constructor is usually used for dependency injection by tests.
	 * @param streamProvider Provides output streams to which to write TE files.
	 * @param recorder Recorder to record TLC as it runs; assumed to already be subscribed.
	 */
	public TraceExpressionSpec(
			IStreamProvider streamProvider,
			ErrorTraceMessagePrinterRecorder recorder) {
		this.outputDirectory = Paths.get(".");
		this.streamProvider = streamProvider;
		this.recorder = recorder;
	}
	
	/**
	 * Returns path to directory to which TE spec will be written.
	 * @return Path to directory to which TE spec will be written.
	 */
	public Path getOutputDirectory() {
		return this.outputDirectory;
	}
	
	/**
	 * Generates the TE spec and writes it to TLA and CFG files.
	 * @param specInfo Information about the original spec.
	 */
	public void generate(ITool specInfo) {
		this.recorder.getMCErrorTrace().ifPresent(errorTrace -> {
			MP.printMessage(EC.TLC_TE_SPEC_GENERATION_START);
			ModelConfig cfg = specInfo.getModelConfig();
			SpecProcessor spec = specInfo.getSpecProcessor();
			String originalSpecName = specInfo.getRootName();
			List<String> variables = Arrays.asList(TLCState.Empty.getVarsAsStrings());
			MCParserResults parserResults = MCParser.generateResultsFromProcessorAndConfig(spec, cfg);
			List<String> constants = parserResults.getModelConfig().getRawConstants();
			if (this.generate(originalSpecName, constants, variables, errorTrace)) {
				MP.printMessage(EC.TLC_TE_SPEC_GENERATION_END, this.getOutputDirectory().toString());
			} else {
				MP.printMessage(EC.TLC_TE_SPEC_GENERATION_ERROR);
			}
		});
	}

	/**
	 * Generates the TE spec and writes it to TLA and CFG files.
	 * @param originalSpecName Name of the original spec.
	 * @param constants Constants from the original spec; to be put into cfg file.
	 * 	example value: { "CONSTANT X <- XVal", "CONSTANT Y <- YVAL" }
	 * @param variables Variables from the original spec.
	 * 	example value: { "x", "y" }
	 * @param errorTrace The error trace.
	 * 
	 * @return Whether TE spec generation was successful.
	 */
	public boolean generate(
			String originalSpecName,
			List<String> constants,
			List<String> variables,
			MCError errorTrace) {
		try (
				OutputStream tlaStream = this.streamProvider.getTlaStream();
				OutputStream cfgStream = this.streamProvider.getCfgStream();
		) {
			TraceExplorer.writeSpecTEStreams(
					originalSpecName,
					constants,
					variables,
					errorTrace,
					tlaStream,
					cfgStream);
			return true;
		} catch (SecurityException | IOException e) {
			MP.printError(
					EC.SYSTEM_UNABLE_TO_OPEN_FILE,
					new String[] {
						this.getOutputDirectory().toString(),
						e.toString()
					});
			return false;
		}
	}
	
	/**
	 * Interface for creating streams to which to write the TE spec.
	 */
	public interface IStreamProvider {
		
		/**
		 * Creates an output stream to which to write the TE spec.
		 * Caller is responsible for managing stream lifecycle.
		 * @return A new output stream to which to write the TE spec.
		 * @throws FileNotFoundException Thrown if filepath is inaccessible.
		 * @throws SecurityException Thrown if lacking perms to write file.
		 */
		public OutputStream getTlaStream() throws FileNotFoundException, SecurityException;
		
		/**
		 * Creates an output stream to which to write the TE spec's CFG file.
		 * Caller is responsible for managing stream lifecycle.
		 * @return A new output stream to which to write the CFG file.
		 * @throws FileNotFoundException Thrown if filepath is inaccessible.
		 * @throws SecurityException Thrown if lacking perms to write file.
		 */
		public OutputStream getCfgStream() throws FileNotFoundException, SecurityException;
	}
	
	/**
	 * Provides streams to actual files on disk.
	 */
	public class FileStreamProvider implements IStreamProvider {
		
		/**
		 * Directory to which to output the files.
		 */
		private Path outputDirectory;
		
		public FileStreamProvider(Path outputDirectory) {
			this.outputDirectory = outputDirectory;
		}
		
		@Override
		public OutputStream getTlaStream() throws FileNotFoundException, SecurityException {
			this.ensureDirectoryExists();
			final File tlaFile = this.outputDirectory.resolve(
					TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME
					+ TLAConstants.Files.TLA_EXTENSION).toFile();
			return new FileOutputStream(tlaFile);
		}
		
		@Override
		public OutputStream getCfgStream() throws FileNotFoundException, SecurityException {
			this.ensureDirectoryExists();

			final File cfgFile = this.outputDirectory.resolve(
					TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME
					+ TLAConstants.Files.CONFIG_EXTENSION).toFile();
			return new FileOutputStream(cfgFile);
		}
		
		/**
		 * Recursively creates directories until the desired path is present.
		 * @throws SecurityException Access issue when creating directories.
		 */
		private void ensureDirectoryExists() throws SecurityException {
			for (int i = 1; i <= this.outputDirectory.getNameCount(); i++) {
				Path subPath = this.outputDirectory.subpath(0, i);
				if (!subPath.toFile().exists()) {
					subPath.toFile().mkdir();
				}
			}
		}
	}
}
