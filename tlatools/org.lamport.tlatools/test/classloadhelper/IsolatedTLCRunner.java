package classloadhelper;

import tlc2.TLC;
import tlc2.TraceExplorationSpecGenerationReport;
import tlc2.model.MCError;
import tlc2.model.MCState;
import tlc2.model.MCVariable;

import java.io.OutputStream;
import java.io.PrintStream;
import java.lang.reflect.InvocationTargetException;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Optional;

/**
 * Runs TLC by loading all its dependencies through an isolated classloader;
 * this enables us to run it multiple times in the same process, by disposing
 * the classloader and loading all the TLC classes again to re-initialize the
 * static variables. Hopefully one day we will go through TLC and remove all
 * the static variables, so all that is required to refresh TLC is create a
 * new instance of the TLC class.
 */
public class IsolatedTLCRunner {
	
	/**
	 * Classloader which loads TLC classes in isolation.
	 */
	private DynamicClassLoader loader;
	
	/**
	 * Instance of the {@link tlc2.TLC} class in the classloader.
	 */
	private Object tlcInstance;
	
	/**
	 * Creates a new instance of this class.
	 * @param printConsoleOutput Whether to have TLC print output to console.
	 */
	public IsolatedTLCRunner(boolean printConsoleOutput) {
		try {
			// Create a new dynamic class loader to load TLC in isolation
			URI tlcUri = TLC.class.getResource("TLC.class").toURI();
			Path tlaToolsDir = Paths.get(tlcUri).getParent().getParent();
			this.loader = new DynamicClassLoader(tlaToolsDir);

			// Initializes the TLC class in this isolated classloader
			try {
				Class<?> tlcClassHandle = this.loader.load("tlc2.TLC");
				this.tlcInstance = ReflectUtil.construct(tlcClassHandle);
			} catch (InvocationTargetException e) {
				e.getCause().printStackTrace();
			}
			
			// Silences output as requested
			if (!printConsoleOutput) {
				PrintStream nullOut = new PrintStream(OutputStream.nullOutputStream());
				Class<?> toolIOClassHandle = this.loader.load("util.ToolIO");
				ReflectUtil.setStaticFieldValue(toolIOClassHandle, "out", nullOut);
			}

		} catch (URISyntaxException e) {
			throw new RuntimeException(e);
		}
	}
	
	/**
	 * Initializes TLC.
	 * @param searchDirs Directories in which to look for TLA files.
	 * @param args TLC command-line parameters.
	 * @return Whether initialization was successful.
	 */
	public boolean initialize(String[] searchDirs, String[] args) {
		// Registers search directories with TLC
		Class<?> tlcClassHandle = this.loader.load("tlc2.TLC");
		Class<?> simpleResolverHandle = this.loader.load("util.SimpleFilenameToStream");
		try {
			Object resolver = ReflectUtil.constructWithParams(
					simpleResolverHandle,
					new Class<?>[] { String[].class },
					new Object[] { searchDirs });
			ReflectUtil.invokeMethodByName(
					tlcClassHandle,
					"setResolver",
					this.tlcInstance,
					new Object[] { resolver });
			
			// Invokes the {@link tlc2.TLC#handleParameters} method
			return (boolean)ReflectUtil.invokeMethodWithParams(
					tlcClassHandle,
					"handleParameters",
					this.tlcInstance,
					new Class<?>[] { String[].class },
					new Object[] { args });
		} catch (InvocationTargetException e) {
			e.getCause().printStackTrace();
		}
		
		return false;
	}
	
	/**
	 * Runs TLC.
	 * @return An error trace, if an error occurred.
	 */
	@SuppressWarnings("unchecked")
	public Optional<MCError> run() {
		try {
			// Invokes the {@link tlc2.TLC#process} method
			Class<?> tlcClassHandle = this.loader.load("tlc2.TLC");
			ReflectUtil.invokeMethod(tlcClassHandle, "process", this.tlcInstance);

			// Retrieves (optional) error from TLC
			Optional<Object> errorTrace = (Optional<Object>)ReflectUtil.invokeMethod(
					tlcClassHandle,
					"getErrorTrace",
					this.tlcInstance);
			return errorTrace.map(trace -> this.convertLoadedMCErrorToMCError(trace));
		} catch (InvocationTargetException e) {
			e.getCause().printStackTrace();
			return Optional.empty();
		}
	}
	
	/**
	 * Gets the TE spec generation report.
	 * @return The TE spec generation report, if it exists.
	 */
	@SuppressWarnings("unchecked")
	public Optional<TraceExplorationSpecGenerationReport> getTESpecGenerationReport() {
		try {
			Class<?> tlcClassHandle = this.loader.load("tlc2.TLC");
			Optional<Object> opReport = (Optional<Object>)ReflectUtil.invokeMethod(
					tlcClassHandle,
					"getTraceExplorationSpecGenerationReport",
					this.tlcInstance);

			return opReport.map(clReport -> {
				Class<?> reportClassHandle = this.loader.load("tlc2.TraceExplorationSpecGenerationReport");
				MCError trace = convertLoadedMCErrorToMCError(ReflectUtil.getFieldValue(reportClassHandle, clReport, "errorTrace"));
				Path tlaPath = (Path)ReflectUtil.getFieldValue(reportClassHandle, clReport, "teSpecTlaPath");
				Path cfgPath = (Path)ReflectUtil.getFieldValue(reportClassHandle, clReport, "teSpecCfgPath");
				return new TraceExplorationSpecGenerationReport(trace, tlaPath, cfgPath);
			});
		} catch (InvocationTargetException e) {
			e.getCause().printStackTrace();
			return Optional.empty();
		}
	}
	
	/**
	 * The {@link tlc2.model.MCError} instance created in the dynamic
	 * classloader is a completely different class (in Java's perspective)
	 * from the MCError instance we have access to in the default classloader;
	 * thus we must convert between them.
	 * @param clErrorTrace The error trace from the dynamic classloader.
	 * @return An equivalent error trace in the default classloader.
	 */
	@SuppressWarnings("unchecked")
	private MCError convertLoadedMCErrorToMCError(Object clErrorTrace) {
		try {
			Class<?> mcErrorClassHandle = this.loader.load("tlc2.model.MCError");
			Class<?> mcStateHandle = this.loader.load("tlc2.model.MCState");
			Class<?> mcVariableHandle = this.loader.load("tlc2.model.MCVariable");

			MCError errorTrace = new MCError();
			List<Object> dMCStates = (List<Object>)ReflectUtil.invokeMethod(mcErrorClassHandle, "getStates", clErrorTrace);
			for (Object dMCState : dMCStates) {
				int stateNumber = (int)ReflectUtil.invokeMethod(mcStateHandle, "getStateNumber", dMCState);
				boolean isStuttering = (boolean)ReflectUtil.invokeMethod(mcStateHandle, "isStuttering", dMCState);
				boolean isBackToState = (boolean)ReflectUtil.invokeMethod(mcStateHandle, "isBackToState", dMCState);
				Object[] dMCVars = (Object[])ReflectUtil.invokeMethod(mcStateHandle, "getVariables", dMCState);
				MCVariable[] vars = new MCVariable[dMCVars.length];
				for (int i = 0; i < dMCVars.length; i++) {
					String varName = (String)ReflectUtil.invokeMethod(mcVariableHandle, "getName", dMCVars[i]);
					String varValue = (String)ReflectUtil.invokeMethod(mcVariableHandle, "getValueAsString", dMCVars[i]);
					vars[i] = new MCVariable(varName, varValue);
				}
				
				MCState state = new MCState(vars, "", "", null, isStuttering, isBackToState, stateNumber);
				errorTrace.addState(state);
			}
			
			return errorTrace;
		} catch (InvocationTargetException e) {
			e.printStackTrace();
			return null;
		}
	}
}
