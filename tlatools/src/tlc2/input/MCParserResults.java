package tlc2.input;

import java.util.List;

import tla2sany.st.Location;
import tlc2.model.MCError;

public class MCParserResults {
	private final String moduleName;
	
	private final MCError error;
	private final List<MCOutputMessage> outputMessages;

	private final List<String> extendedModules;

	private final List<Location> initNextLocationsToDelete;

	private final boolean behaviorIsInitNext;
	
	MCParserResults(final String rootModuleName, final MCError mcError, final List<MCOutputMessage> messages,
			final List<String> extendeds, final List<Location> initNextLocations, final boolean wasInitNext) {
		moduleName = rootModuleName;
		
		error = mcError;
		outputMessages = messages;
		
		extendedModules = extendeds;
		
		initNextLocationsToDelete = initNextLocations;
		
		behaviorIsInitNext = wasInitNext;
	}
	
	public String getModuleName() {
		return moduleName;
	}

	public MCError getError() {
		return error;
	}
	
	public List<MCOutputMessage> getOutputMessages() {
		return outputMessages;
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
