package tlc2.input;

import java.util.List;
import java.util.Set;

import tla2sany.st.Location;
import tlc2.model.MCError;
import tlc2.tool.impl.ModelConfig;

public class MCParserResults {
	private final String moduleName;
	
	private MCError error;
	private List<MCOutputMessage> outputMessages;

	private final List<String> immediateExtendedModules;
	private final Set<String> allExtendedModules;

	private final List<Location> initNextLocationsToDelete;

	private final boolean behaviorIsInitNext;
	
	private final String originalNextOrSpecificationName;
	
	private final ModelConfig modelConfig;

	MCParserResults(final String rootModuleName, final List<String> immediateExtendeds, final Set<String> allExtendeds,
					final List<Location> initNextLocations, final boolean wasInitNext, final String nextOrSpecName,
					final ModelConfig config) {
		moduleName = rootModuleName;
		
		immediateExtendedModules = immediateExtendeds;
		allExtendedModules = allExtendeds;
		
		initNextLocationsToDelete = initNextLocations;
		
		behaviorIsInitNext = wasInitNext;
		
		originalNextOrSpecificationName = nextOrSpecName;
		
		modelConfig = config;
	}
	
	MCParserResults(final String rootModuleName, final MCError mcError, final List<MCOutputMessage> messages,
					final List<String> immediateExtendeds, final Set<String> allExtendeds,
					final List<Location> initNextLocations, final boolean wasInitNext, final String nextOrSpecName,
					final ModelConfig config) {
		this(rootModuleName, immediateExtendeds, allExtendeds, initNextLocations, wasInitNext, nextOrSpecName, config);
		
		error = mcError;
		outputMessages = messages;
	}
	
	public ModelConfig getModelConfig() {
		return modelConfig;
	}
	
	public String getModuleName() {
		return moduleName;
	}
	
	public String getOriginalNextOrSpecificationName() {
		return originalNextOrSpecificationName;
	}

	public MCError getError() {
		return error;
	}
	
	void setError(final MCError mcError) {
		error = mcError;
	}
	
	public List<MCOutputMessage> getOutputMessages() {
		return outputMessages;
	}
	
	void setOutputMessages(final List<MCOutputMessage> messages) {
		outputMessages = messages;
	}

	/**
	 * @return the {@link List} of all modules extended by the root spec explicitly - in other words, for example,
	 * 				the X, Y, Z cited by a root spec's "EXTENDS X, Y, Z"
	 */
	public List<String> getOriginalExtendedModules() {
		return immediateExtendedModules;
	}
	
	/**
	 * @return the {@link Set} of all modules extended - in other words, the modules extended by all modules extended
	 * 				by all modules extended by ... the root spec.
	 */
	public Set<String> getAllExtendedModules() {
		return allExtendedModules;
	}

	/**
	 * @return ordered from location first in document to that which is last in document
	 */
	public List<Location> getInitNextLocationsToDelete() {
		return initNextLocationsToDelete;
	}

	public boolean isBehaviorInitNext() {
		return behaviorIsInitNext;
	}
}
