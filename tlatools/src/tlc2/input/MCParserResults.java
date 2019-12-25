package tlc2.input;

import java.util.List;

import tla2sany.st.Location;
import tlc2.model.MCError;

public class MCParserResults {
	private final String moduleName;
	
	private MCError error;
	private List<MCOutputMessage> outputMessages;

	private final List<String> extendedModules;

	private final List<Location> initNextLocationsToDelete;

	private final boolean behaviorIsInitNext;
	
	private final String originalNextOrSpecificationName;

	MCParserResults(final String rootModuleName, final List<String> extendeds, final List<Location> initNextLocations,
					final boolean wasInitNext, final String nextOrSpecName) {
		moduleName = rootModuleName;
		
		extendedModules = extendeds;
		
		initNextLocationsToDelete = initNextLocations;
		
		behaviorIsInitNext = wasInitNext;
		
		originalNextOrSpecificationName = nextOrSpecName;
	}
	
	MCParserResults(final String rootModuleName, final MCError mcError, final List<MCOutputMessage> messages,
					final List<String> extendeds, final List<Location> initNextLocations, final boolean wasInitNext,
					final String nextOrSpecName) {
		this(rootModuleName, extendeds, initNextLocations, wasInitNext, nextOrSpecName);
		
		error = mcError;
		outputMessages = messages;
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

	public List<String> getExtendedModules() {
		return extendedModules;
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
