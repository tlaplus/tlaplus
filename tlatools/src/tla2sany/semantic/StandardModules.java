/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tla2sany.semantic;

import java.util.HashSet;
import java.util.Set;

public class StandardModules {
	private static final Set<String> STANDARD_MODULES = new HashSet<>();
	
	static {
		// Quick'n'Dirty hack! This breaks if any one of the operators is override by
		// the model or a complete standard module has been replaced by a user-defined
		// module with the same name.
		STANDARD_MODULES.add("FiniteSets");
		STANDARD_MODULES.add("Sequences");
		STANDARD_MODULES.add("Bags");
		STANDARD_MODULES.add("Naturals");
		STANDARD_MODULES.add("Integers");
		STANDARD_MODULES.add("Reals");
		STANDARD_MODULES.add("RealTime");
		STANDARD_MODULES.add("Randomization");
		STANDARD_MODULES.add("TLC");
	}

	private StandardModules() {
		// no instances
	}
	
	public static boolean isDefinedInStandardModule(SemanticNode sn) {
		if ((sn != null) && (sn.getLocation() != null)) {
			return isDefinedInStandardModule(sn.getLocation().source()); // source might be null
		}
		return false;
	}
	
	public static boolean isDefinedInStandardModule(final String moduleName) {
		return STANDARD_MODULES.contains(moduleName);
	}
	
	public static void filterNonStandardModulesFromSet(final Set<String> listOfModules) {
		listOfModules.retainAll(STANDARD_MODULES);
	}
}
