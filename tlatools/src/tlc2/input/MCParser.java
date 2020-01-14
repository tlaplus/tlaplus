package tlc2.input;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolMatcher;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;
import tlc2.model.MCError;
import tlc2.tool.Defns;
import tlc2.tool.impl.ModelConfig;
import tlc2.tool.impl.SpecProcessor;
import tlc2.tool.impl.SymbolNodeValueLookupProvider;
import tlc2.tool.impl.TLAClass;
import util.FilenameToStream;
import util.SimpleFilenameToStream;
import util.TLAConstants;

/**
 * This class parses the triplet of .out, .cfg, and .tla files - typically thought of as MC.out, MC.cfg, MC.tla, but
 * 	not required to be such.
 */
public class MCParser {
	private static final int TOOL_ID = 0;
	
	/**
	 * @param specProcessor
	 * @param modelConfig
	 * @return an instance of {@link MCParserResults} with neither error nor output messages set, yet
	 */
	public static MCParserResults generateResultsFromProcessorAndConfig(final SpecProcessor specProcessor,
																		final ModelConfig modelConfig) {
		final String rootModuleName;
		final String nextOrSpecName;
		final ArrayList<Location> initNextLocationsToDelete = new ArrayList<>();
		final boolean isInitNext = !modelConfig.configDefinesSpecification();
		final ModuleNode root = specProcessor.getRootModule();
		if (isInitNext) {
			final String initDefinitionName = modelConfig.getInit();
			nextOrSpecName = modelConfig.getNext();
			final Collection<SymbolNode> initNodes = root.getSymbols(new NodeNameMatcher(initDefinitionName));
			final Collection<SymbolNode> nextNodes = root.getSymbols(new NodeNameMatcher(nextOrSpecName));

			if (initNodes.size() == 1) {
				final OpDefNode initNode = (OpDefNode) initNodes.iterator().next();

				if (initNode.getOriginallyDefinedInModuleNode().equals(root)) {
					initNextLocationsToDelete.add(initNode.getLocation());
				}
				// else it is defined in a module which the original spec is extending.. nothing to document
			}

			if (nextNodes.size() == 1) {
				final OpDefNode nextNode = (OpDefNode) nextNodes.iterator().next();

				if (nextNode.getOriginallyDefinedInModuleNode().equals(root)) {
					initNextLocationsToDelete.add(nextNode.getLocation());
				}
				// else it is defined in a module which the original spec is extending.. nothing to document
			}
		} else {
			nextOrSpecName = modelConfig.getSpec();
		}
		initNextLocationsToDelete.sort(new LocationComparator());

		final ArrayList<String> extendees = new ArrayList<>();
		root.getExtendedModuleSet(false).stream().forEach(moduleNode -> extendees.add(moduleNode.getName().toString()));

		final HashSet<String> allExtendees = new HashSet<>();
		root.getExtendedModuleSet(true).stream().forEach(moduleNode -> allExtendees.add(moduleNode.getName().toString()));
		
		rootModuleName = root.getName().toString();

		return new MCParserResults(rootModuleName, extendees, allExtendees, initNextLocationsToDelete,
								   isInitNext, nextOrSpecName, modelConfig);
	}	
	
	private final ModelConfig configParser;

	private MCOutputParser outputParser;
	
	private final TLAClass tlaClass;
	private final Defns defns;
	
	private final FilenameToStream resolver;

	private MCParserResults parserResults;
	
	private final String specBaseName;
	
	/**
	 * @param sourceDirectory
	 * @param specName
	 * @param specialCaseOutputFile if non-null, this will be used as the source for the output parser
	 */
	public MCParser(final File sourceDirectory, final String specName) {
		this(sourceDirectory, specName, null);
		
		File f= new File(sourceDirectory, (specBaseName + TLAConstants.Files.OUTPUT_EXTENSION));
		if (!f.exists()) {
			throw new IllegalArgumentException("No readable output file could be found at " + f.getAbsolutePath());
		}
		
		outputParser = new MCOutputParser(f);
		
		f = new File(sourceDirectory, (specBaseName + TLAConstants.Files.TLA_EXTENSION));
		if (!f.exists()) {
			throw new IllegalArgumentException("No readable TLA file could be found at " + f.getAbsolutePath());
		}
	}
	
	/**
	 * @param sourceDirectory
	 * @param specName
	 * @param ignoreOutputParse if this is true, no output parsing will be done by this instance; the results returned
	 * 			by {@link #parse()} will contain no output messages nor any potential {@code MCError}
	 */
	public MCParser(final File sourceDirectory, final String specName, final boolean ignoreOutputParse) {
		this(sourceDirectory, specName, null);

		if (!ignoreOutputParse) {
			final File f = new File(sourceDirectory, (specBaseName + TLAConstants.Files.OUTPUT_EXTENSION));
			if (!f.exists()) {
				throw new IllegalArgumentException("No readable output file could be found at " + f.getAbsolutePath());
			}
			
			outputParser = new MCOutputParser(f);
		}
		
		final File f = new File(sourceDirectory, (specBaseName + TLAConstants.Files.TLA_EXTENSION));
		if (!f.exists()) {
			throw new IllegalArgumentException("No readable TLA file could be found at " + f.getAbsolutePath());
		}
	}
	
	private MCParser(final File sourceDirectory, final String specName, final Object signatureDifferentiator) {
		resolver = new SimpleFilenameToStream(sourceDirectory.getAbsolutePath());
		specBaseName = specName;
		
		final File f = new File(sourceDirectory, (specBaseName + TLAConstants.Files.CONFIG_EXTENSION));
		if (!f.exists()) {
			throw new IllegalArgumentException("No readable config file could be found at " + f.getAbsolutePath());
		}
		configParser = new ModelConfig(f.getAbsolutePath(), resolver);
		
		tlaClass = new TLAClass("tlc2.module", resolver);
		defns = new Defns();
	}
	
	/**
	 * @return will return null until {@link #parse()} has been run successfully
	 */
	public MCParserResults getParseResults() {
		return parserResults;
	}

	/**
	 * @return an instance of {@link MCParserResults} representing the results. If
	 *         this instance was constructed via
	 *         {@link #MCParser(File, String, boolean)} with the third argument
	 *         {@code true} then the results returned will contain no output
	 *         messages nor any potential {@code MCError}
	 * @throws IllegalStateException if parse has already been called on this
	 *                               instance
	 */
	public MCParserResults parse() {
		if (parserResults != null) {
			throw new IllegalStateException("Parse has already been called.");
		}
		
		try {
			final List<MCOutputMessage> encounteredMessages = (outputParser != null) ? outputParser.parse(true) : null;

			configParser.parse();

			// No reason to start-up SANY if we're not going to generate something because the output file is unusable
			if ((encounteredMessages == null) || (encounteredMessages.size() > 0)) {
				final SymbolNodeValueLookupProvider defaultLookup = new SymbolNodeValueLookupProvider() {};
				final SpecProcessor specProcessor = new SpecProcessor(specBaseName, resolver, TOOL_ID, defns,
																	  configParser, defaultLookup, null, tlaClass);
				parserResults = generateResultsFromProcessorAndConfig(specProcessor, configParser);
				
				if (outputParser != null) {
					parserResults.setError(outputParser.getError());
					parserResults.setOutputMessages(encounteredMessages);
				}
			} else {
				// we'll have a zero size if the output generated came from a TLC run that did not have the '-tool' flag
				parserResults = new MCParserResults(null, ((outputParser != null) ? outputParser.getError() : null),
													encounteredMessages, new ArrayList<>(), new HashSet<>(),
													new ArrayList<>(), true, null, configParser);
			}
			
			return parserResults;
		} catch (final IOException e) {
			System.out.println("Caught exception while performing MC parsing: " + e.getMessage());
			e.printStackTrace();
		}

		return null;
	}

	
	public static void main(final String[] args) throws Exception {
		final MCParser parser = new MCParser(new File(args[0]), TLAConstants.Files.MODEL_CHECK_FILE_BASENAME, null);
		final MCParserResults results = parser.parse();
		
		System.out.println("Parse encountered " + results.getOutputMessages().size() + " messages.");
		final MCError error = results.getError();
		if (error != null) {
			System.out.println("Encountered error: ");
			System.out.println(error.toSequenceOfRecords(true));
		}
		
		final List<String> extendedModules = results.getOriginalExtendedModules();
		System.out.println("Found " + extendedModules.size() + " module(s) being extended explicitly by the root spec:");
		for (final String module : extendedModules) {
			System.out.println("\t" + module);
		}
	}
	
	
	private static class NodeNameMatcher implements SymbolMatcher {
		private final String name;
		
		NodeNameMatcher(final String nameToMatch) {
			name = nameToMatch;
		}

		@Override
		public boolean matches(final SymbolNode aSymbol) {
			if (aSymbol.getName() != null) {
				return name.equals(aSymbol.getName().toString());
			}
			return false;
		}
	}
	
	
	// orders from location first in document to that which is last in document
	private static class LocationComparator implements Comparator<Location> {
		@Override
		public int compare(final Location l2, final Location l1) {
			if (l1.beginLine() == l2.beginLine()) {
				if (l1.beginColumn() != l2.beginColumn()) {
					return l1.beginColumn() - l2.beginColumn();
				}
				
				if (l1.endLine() != l2.endLine()) {
					return l1.endLine() - l2.endLine();
				}
				
				return l1.endColumn() - l2.endColumn();
			}
			
			return l1.beginLine() - l2.beginLine();
		}
	}
}
