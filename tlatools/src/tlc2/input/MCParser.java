package tlc2.input;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
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
	
	
	private final ModelConfig configParser;

	private final MCOutputParser outputParser;
	
	private final TLAClass tlaClass;
	private final Defns defns;
	private SpecProcessor specProcessor;
	
	private final FilenameToStream resolver;

	private MCParserResults parserResults;
	
	private final String specBaseName;
	
	public MCParser(final File sourceDirectory, final String specName) {
		resolver = new SimpleFilenameToStream(sourceDirectory.getAbsolutePath());
		specBaseName = specName;
		
		File f = new File(sourceDirectory, (specBaseName + TLAConstants.Files.CONFIG_EXTENSION));
		if (!f.exists()) {
			throw new IllegalArgumentException("No readable config file could be found at " + f.getAbsolutePath());
		}
		configParser = new ModelConfig(f.getAbsolutePath(), resolver);
		
		f = new File(sourceDirectory, (specBaseName + TLAConstants.Files.OUTPUT_EXTENSION));
		if (!f.exists()) {
			throw new IllegalArgumentException("No readable output file could be found at " + f.getAbsolutePath());
		}
		outputParser = new MCOutputParser(f);
		
		f = new File(sourceDirectory, (specBaseName + TLAConstants.Files.TLA_EXTENSION));
		if (!f.exists()) {
			throw new IllegalArgumentException("No readable TLA file could be found at " + f.getAbsolutePath());
		}
		
		tlaClass = new TLAClass("tlc2.module", resolver);
		defns = new Defns();
	}

	/**
	 * @return an instance of {@link MCParserResults} representing the results
	 * @throws IllegalStateException if parse has already been called on this instance
	 */
	public MCParserResults parse() {
		if (parserResults != null) {
			throw new IllegalStateException("Parse has already been called.");
		}
		
		try {
			final List<MCOutputMessage> encounteredMessages = outputParser.parse(true);

			configParser.parse();

			final String rootModuleName;
			final String nextOrSpecName;
			final ArrayList<String> extendees = new ArrayList<>();
			final ArrayList<Location >initNextLocationsToDelete = new ArrayList<>();
			final boolean isInitNext = !configParser.configDefinesSpecification();
			// No reason to start-up SANY if we're not going to generate something because the output file is unusable
			if (encounteredMessages.size() > 0) {
				final SymbolNodeValueLookupProvider defaultLookup = new SymbolNodeValueLookupProvider() {};
				specProcessor = new SpecProcessor(specBaseName, resolver, TOOL_ID, defns, configParser,
												  defaultLookup, null, tlaClass);

				final ModuleNode root = specProcessor.getRootModule();
				if (isInitNext) {
					final String initDefinitionName = configParser.getInit();
					nextOrSpecName = configParser.getNext();
					final Collection<SymbolNode> initNodes = root.getSymbols(new NodeNameMatcher(initDefinitionName));
					final Collection<SymbolNode> nextNodes = root.getSymbols(new NodeNameMatcher(nextOrSpecName));
					
					if (initNodes.size() == 1) {
						final OpDefNode initNode = (OpDefNode)initNodes.iterator().next();
						
						if (initNode.getOriginallyDefinedInModuleNode().equals(root)) {
							initNextLocationsToDelete.add(initNode.getLocation());
						}
						// else it is defined in a module MC is extending.. nothing to clean up
					}
					
					if (nextNodes.size() == 1) {
						final OpDefNode nextNode = (OpDefNode)nextNodes.iterator().next();
						
						if (nextNode.getOriginallyDefinedInModuleNode().equals(root)) {
							initNextLocationsToDelete.add(nextNode.getLocation());
						}
						// else it is defined in a module MC is extending.. nothing to clean up
					}
				} else {
					nextOrSpecName = configParser.getSpec();
				}
				initNextLocationsToDelete.sort(new LocationComparator());
				
				root.getExtendedModuleSet(false).stream().forEach(moduleNode -> extendees.add(moduleNode.getName().toString()));
				rootModuleName = root.getName().toString();
			} else {
				// we'll have a zero size if the output generated came from a TLC run that did not have the '-tool' flag
				rootModuleName = null;
				nextOrSpecName = null;
			}
			
			parserResults = new MCParserResults(rootModuleName, outputParser.getError(),
												encounteredMessages, extendees, initNextLocationsToDelete,
												isInitNext, nextOrSpecName);
			
			return parserResults;
		} catch (final IOException e) {
			System.out.println("Caught exception while performing MC parsing: " + e.getMessage());
			e.printStackTrace();
			specProcessor = null;
		}

		return null;
	}

	
	public static void main(final String[] args) throws Exception {
		final MCParser parser = new MCParser(new File(args[0]), TLAConstants.Files.MODEL_CHECK_FILE_BASENAME);
		final MCParserResults results = parser.parse();
		
		System.out.println("Parse encountered " + results.getOutputMessages().size() + " messages.");
		final MCError error = results.getError();
		if (error != null) {
			System.out.println("Encountered error: ");
			System.out.println(error.toSequenceOfRecords(true));
		}
		
		final List<String> extendedModules = results.getExtendedModules();
		System.out.println("Found " + extendedModules.size() + " module(s) being extended:");
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
