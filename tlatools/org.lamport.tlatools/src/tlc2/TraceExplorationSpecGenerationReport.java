package tlc2;

import java.nio.file.Path;

import tlc2.model.MCError;

/**
 * Information about the generated TE spec.
 */
public class TraceExplorationSpecGenerationReport {
	
	/**
	 * The error trace reproduced by the TE spec.
	 */
	public MCError errorTrace;
	
	/**
	 * Path to the TE spec TLA file.
	 */
	public Path teSpecTlaPath;
	
	/**
	 * Path to the TE spec CFG file.
	 */
	public Path teSpecCfgPath;
	
	/**
	 * Initializes a new instance of {@link GenerationReport}
	 * @param errorTrace The error trace.
	 * @param teSpecTlaPath The TLA path.
	 * @param teSpecCfgPath The CFG path.
	 */
	public TraceExplorationSpecGenerationReport(MCError errorTrace, Path teSpecTlaPath, Path teSpecCfgPath) {
		this.errorTrace = errorTrace;
		this.teSpecTlaPath = teSpecTlaPath;
		this.teSpecCfgPath = teSpecCfgPath;
	}
}
