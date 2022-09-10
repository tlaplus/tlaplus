package tlc2;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Date;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import tlc2.model.MCError;
import tlc2.model.MCState;
import tlc2.output.EC;
import tlc2.output.ErrorTraceMessagePrinterRecorder;
import tlc2.output.MP;
import tlc2.output.SpecTraceExpressionWriter;
import tlc2.tool.Defns;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.impl.ModelConfig;
import tlc2.value.impl.ModelValue;
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
	 * 
	 * @param output    Directory to which to output the TE spec.
	 * @param timestamp Timestamp to include in TE spec filename.
	 * @param recorder  Recorder to record TLC as it runs; assumed to already be
	 *                  subscribed.
	 */
	public TraceExplorationSpec(Path output, Date timestamp, String originalModuleName,
			ErrorTraceMessagePrinterRecorder recorder) {
		this.outputPath = output;
		this.teSpecModuleName = deriveTESpecModuleName(originalModuleName, timestamp);
		this.originalModuleName = originalModuleName;
		this.recorder = recorder;
	}

	public TraceExplorationSpec(Path output, String teModuleName, String originalModuleName,
			ErrorTraceMessagePrinterRecorder recorder) {
		this.outputPath = output;
		this.teSpecModuleName = teModuleName;
		this.originalModuleName = originalModuleName;
		this.recorder = recorder;
	}

	public void generate(ITool specInfo) {
		if (this.recorder.getMCErrorTrace().isEmpty()) {
			return;
		}
		final MCError errorTrace = this.recorder.getMCErrorTrace().get();
		// TODO Handle the case that TLC threw an unexpected exception, which generally
		// translates into EC.General and should be interceptable with a
		// tlc2.output.IMessagePrinterRecorder.
		// If TLC started from a checkpoint (`-recover`), we don't want to generate a TE
		// spec.
		if ((errorTrace.getStates().size() <= 1)
				|| (TLCGlobals.mainChecker != null && TLCGlobals.mainChecker.isRecovery())) {
			return;
		}

		final List<String> variables = Arrays.asList(TLCState.Empty.getVarsAsStrings());

		// Create any intermediate folders if they don't exist.
		this.outputPath.toFile().mkdirs();

		final Path teSpecPath = this.outputPath.resolve(teSpecModuleName + TLAConstants.Files.TLA_EXTENSION);
		try (OutputStream tlaStream = new FileOutputStream(teSpecPath.toFile());) {
			writeSpecTEStreams(teSpecModuleName, originalModuleName, specInfo.getModelConfig(), variables, errorTrace,
					specInfo, tlaStream);
			MP.printMessage(EC.TLC_TE_SPEC_GENERATION_COMPLETE, teSpecPath.toString());
		} catch (SecurityException | IOException e) {
			MP.printMessage(EC.TLC_TE_SPEC_GENERATION_ERROR, e.getMessage());
		}
	}

	private void writeSpecTEStreams(final String teSpecModuleName, final String originalSpecName,
			final ModelConfig modelConfig, final List<String> variables, final MCError error, final ITool specInfo,
			final OutputStream specTETLAOutStream) throws IOException {

		final List<MCState> trace = error.getStates();

		final SpecTraceExpressionWriter writer = new SpecTraceExpressionWriter();

		// It is tempting to lookup the constant defns in the SpecProcessor instead of
		// going through the mumbo-jumbo of parsing and converting entries in
		// ModelConfig. However, the constant defns have already been evaluated by
		// SpecProcessor and turned into IValue instances. Serializing those IValue
		// instances via their toString method will probably cause invalid config
		// values. Additionally, the constant defns are a superset of what is in
		// declared and defined in ModelConfig.
		final List<List<String>> constants = modelConfig.getConstantsAsList();

		// The original spec might declare model-values implicitly by just declaring a
		// set of model-values. This works for the original spec as long as those
		// model-values do not appear explicitly. However, the model-values will
		// likely appear in the error-trace, which is why the trace spec has to
		// declare them. Imagine, for example, a CONSTANT P in the spec and a CONSTANT P
		// = {p1,p2} in the config (e.g. modeling a set of two processes) and an
		// error-trace that shows one process to enter some critical section.
		// Add all the model values as constants, they have to be reified (to mean
		// something) in a TLA module.
		// First we set all the model values seen, the values will be at the static
		// field ModelValue.mvs.
		ModelValue.setValues();
		final Set<String> declaredConstantNames = constants.stream().map(l -> l.get(0)).collect(Collectors.toSet());
		final Set<ModelValue> reifiedConstants = new HashSet<ModelValue>();
		reifiedConstants.addAll(Arrays.asList(ModelValue.mvs));
		reifiedConstants.stream().filter(m -> !declaredConstantNames.contains(m.toString()))
				.collect(Collectors.toSet());

		/**
		 * Write content of config file (SpecTE).
		 * <p>
		 * Contrary to the Toolbox's TraceExplorerDelegate, which reads constants,
		 * overrides, ... from the TLC model, this implementation copies all CONSTANT
		 * and CONSTANTS verbatim from the existing config file with which TLC ran. The
		 * definition that appear in the .tla file (e.g. MC.tla) don't have to be copied
		 * because SpecTE extends MC. We also add the model values as constants so they
		 * can be used for the traces at the TLA modules. (see
		 * TraceExplorerDelegate#writeModelInfo)
		 */

		List<String> indentedConstants = new ArrayList<String>();
		// Ordinary constants:
		for (List<String> keyValuePair : constants) {
			if (keyValuePair.size() > 1) {
				String key = keyValuePair.get(0).toString();
				String value = keyValuePair.get(1).toString();
				indentedConstants.add(SpecTraceExpressionWriter.indentString(String.format("%s = %s", key, value), 1));
			} else {
				String line = keyValuePair.get(0).toString();
				indentedConstants.add(SpecTraceExpressionWriter.indentString(line, 1));
			}
		}

		// Reified model-values:
		for (ModelValue mv : reifiedConstants) {
			indentedConstants.add(SpecTraceExpressionWriter.indentString(String.format("%s = %s", mv, mv), 1));
		}

		// If it has a lasso, add the TTrace lasso constants to the configuration file.
		if (error.isLasso()) {
			indentedConstants.add(TLAConstants.TraceExplore.SPEC_TETRACE_LASSO_START + " = "
					+ trace.get(trace.size() - 1).getStateNumber());
			indentedConstants.add(TLAConstants.TraceExplore.SPEC_TETRACE_LASSO_END + " = " + (trace.size() - 1));
		}

		writer.addConstants(indentedConstants);

		// If needed, create module which contain the reified constants.
		// First we need to handle the case where a model value is defined in
		// the config file, but, for some reason, it's not used in any of the
		// model specs. E.g. I define `p1 = p1` in the `CONSTANTS` header of the
		// config file, but I do not use it (through `CONSTANTS`) in the model spec.
		// So we add these remaining constants to `mvsStr` so they are added to the
		// `TE` spec.
		Defns defns = specInfo.getSpecProcessor().getDefns();
		ArrayList<String> modConstants = new ArrayList<String>();
		for (ModelValue mv : ModelValue.mvs) {
			if (defns.get(mv.toString()) == null) {
				modConstants.add(mv.toString());
			}
		}
		// If it has a lasso, add the TTrace lasso constants to the modules constants
		// so we can have it in a more convenient place (so other tools, like the
		// Toolbox,
		// can, for example, highlight the lasso).
		if (error.isLasso()) {
			modConstants.add(TLAConstants.TraceExplore.SPEC_TETRACE_LASSO_START);
			modConstants.add(TLAConstants.TraceExplore.SPEC_TETRACE_LASSO_END);
		}
		// Create TEConstant module.
		final String teConstantSpecName = String.format("%s_%s", originalSpecName,
				TLAConstants.TraceExplore.SPEC_TECONSTANTS_NAME);
		final Set<String> teConstantModuleHashSet = new HashSet<>();
		teConstantModuleHashSet.add(TLAConstants.BuiltInModules.TLC);
		String modelValuesAsConstants;
		if (!modConstants.isEmpty()) {
			teConstantModuleHashSet.add(teConstantSpecName);
			modelValuesAsConstants = String.format("CONSTANTS %s\n", String.join(", ", modConstants));
		} else {
			modelValuesAsConstants = "";
		}

		/**
		 * Write SpecTE.
		 */
		final Set<String> specTEExtendedModules = new HashSet<>();
		// A TE spec has to extend Toolbox to have access to _TETrace and _TEPosition
		// operators.
		specTEExtendedModules.add(TLAConstants.BuiltInModules.TRACE_EXPRESSIONS);
		specTEExtendedModules.add("TLCExt");
		// EXTEND Naturals for next-state relation:
		// _next ==
		// /\ \E i,j \in DOMAIN _TETrace:
		// /\ \/ j = i + 1 \* <--- Here!
		// /\ x = _TETrace[i].x
		// /\ x' = _TETrace[j].x
		//
		specTEExtendedModules.add("Naturals");
		// Len(..) operator appearing in _inv (not added by the Toolbox because the
		// Toolbox checks deadlock).
		specTEExtendedModules.add("Sequences");
		specTEExtendedModules.addAll(teConstantModuleHashSet);

		writer.addPrimer(teSpecModuleName, originalSpecName, specTEExtendedModules);

		writer.addTraceExpressionInstance(
				String.format("%s_%s", originalSpecName, TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME));

		final String teTraceName = String.format("%s_%s", originalSpecName,
				TLAConstants.TraceExplore.SPEC_TETRACE_NAME);

		writer.addTraceFunctionInstance(teTraceName);

		writer.addProperties(trace, originalSpecName);

		// Write Init and Next with vars instead of extracting the vars from trace to
		// always write a syntactically correct behavior spec even if trace = <<>>.
		writer.addInitNextTraceFunction(trace, teSpecModuleName, variables, modelConfig);

		if (error.isLassoWithDuplicates()) {
			// The same state or states may appear multiple times in a (liveness) trace. For
			// example, a trace could be s -> t -> s -> u with u closing the lasso back to
			// the *first* s. (trace violates e.g. a property s.t. <>[]t \/ <>[]u. In other
			// words, t and u are mutually exclusive). Unless we add a VIEW to the trace
			// spec
			// that causes different fingerprints for the s states to be calculated, the
			// trace won't be recreated. The view is such that the start and end states of
			// the lasso get the same value.
			//
			// <<vars, IF TLCGet("level") = _TTraceLassoEnd + 1
			// THEN _TTraceLassoStart
			// ELSE TLCGet("level")>>
			//
			// As an alternative, an auxiliary _index variable could be added to every spec
			// that gets incremented. This would be the explicit variant of TLCGet("level")
			// above.
			// However, that has the risk of runaway traces s.t. _index keeps incrementing
			// forever.
			//
			// /\ \/ /\ _index < _TTraceLassoEnd
			// /\ _index' = _index + 1
			// \/ /\ _index = _TTraceLassoEnd
			// /\ _index' = _TTraceLassoStart
			// /\ x = _TETrace[_index].x
			// /\ x' = _TETrace[_index'].x
			writer.addView(String.join(", ", variables));
		}

		writer.addFooter();

		/**
		 * Write definition of trace expression into new module.
		 */
		writer.append(TLAConstants.CR);

		final SpecTraceExpressionWriter te = new SpecTraceExpressionWriter();
		final String teModuleName = String.format("%s_%s", originalSpecName,
				TLAConstants.TraceExplore.EXPLORATION_MODULE_NAME);
		te.append(TLAConstants.CR);

		writer.append(String.format(" Note that you can extract this module `%s`", teModuleName))
				.append(TLAConstants.CR);
		writer.append("  to a dedicated file to reuse `expression` (the module in the ").append(TLAConstants.CR);
		writer.append(String.format("  dedicated `%s.tla` file takes precedence ", teModuleName))
				.append(TLAConstants.CR);
		writer.append(String.format("  over the module `BlockingQueue_TEExpression` below).", teModuleName));

		te.addPrimer(teModuleName, originalSpecName, specTEExtendedModules);
		te.addTraceExpressionStub(originalSpecName, TLAConstants.TraceExplore.SPEC_TE_TRACE_EXPRESSION, variables);
		te.addFooter();
		writer.append(TLAConstants.CR + te.toString() + TLAConstants.CR + TLAConstants.CR);

		/**
		 * Write commented definition of trace def override into new module. A user
		 * simply has to provide the serialized trace and uncomment the module.
		 */
		writer.append(TLAConstants.CR);
		writer.append("Parsing and semantic processing can take forever if the trace below is long.")
				.append(TLAConstants.CR);
		writer.append(" In this case, it is advised to deserialize the trace from a binary file.")
				.append(TLAConstants.CR);
		writer.append(" To create the file, replace your spec's invariant F with:").append(TLAConstants.CR);
		writer.append("  Inv == IF F THEN TRUE ELSE ~IOSerialize(Trace, \"file.bin\", TRUE)").append(TLAConstants.CR);
		writer.append(" (IOUtils module is from https://modules.tlapl.us/)");

		final Set<String> extendedModulesWithIOUtils = new HashSet<>();
		extendedModulesWithIOUtils.add("IOUtils");
		extendedModulesWithIOUtils.addAll(teConstantModuleHashSet);

		final SpecTraceExpressionWriter w = new SpecTraceExpressionWriter();
		w.append(TLAConstants.CR);
		w.addPrimer(teTraceName, originalSpecName, extendedModulesWithIOUtils);
		w.append(TLAConstants.TraceExplore.SPEC_TETRACE_TRACE_DEF).append(TLAConstants.DEFINES)
				.append("IODeserialize(\"file.bin\", TRUE)\n\n");
		w.addFooter();
		// Users can uncomment the module if they wish to read the serialized trace.
		writer.append(TLAConstants.CR + w.getComment() + TLAConstants.CR + TLAConstants.CR);

		/**
		 * Write definition of trace def into new module.
		 */
		final Set<String> teTraceExtendedModules = new HashSet<>();
		teTraceExtendedModules.addAll(teConstantModuleHashSet);
		writer.addPrimer(teTraceName, originalSpecName, teTraceExtendedModules);

		writer.addTraceFunction(trace, TLAConstants.TraceExplore.SPEC_TETRACE_TRACE_DEF,
				TLAConstants.TraceExplore.SPEC_TETRACE_TRACE);

		writer.addAliasToCfg(TLAConstants.TraceExplore.SPEC_TE_TTRACE_EXPRESSION);

		/**
		 * Write TEConstants module, if needed.
		 */
		if (!modelValuesAsConstants.isEmpty()) {
			writer.addFooter();
			writer.append(TLAConstants.CR);
			writer.addPrimer(teConstantSpecName, originalSpecName);
			writer.append(modelValuesAsConstants).append(TLAConstants.CR);
		}

		writer.wrapConfig(teSpecModuleName);
		
		/**
		 * Write to streams.
		 */
		writer.writeStreams(specTETLAOutStream, specTETLAOutStream);
	}

	public static String teModuleId(Date timestamp) {
		final long secondsSinceEpoch = timestamp.getTime() / 1_000L;
		return Long.toString(secondsSinceEpoch);
	}

	/**
	 * Derives the TE spec module name.
	 * 
	 * @param ogModuleName Original module name.
	 * @return The TE spec module name.
	 */
	public static String deriveTESpecModuleName(String ogModuleName, Date timestamp) {
		// millis to secondPaths
		return String.format("%s_%s_%s", ogModuleName, TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME,
				teModuleId(timestamp));
	}

	/**
	 * Determines whether the given spec is a TE spec.
	 * 
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
			return filename.matches("^.*_" + TLAConstants.TraceExplore.TRACE_EXPRESSION_MODULE_NAME + ".*(.tla)?$");
		} catch (InvalidPathException e) {
			return false;
		}
	}
}
