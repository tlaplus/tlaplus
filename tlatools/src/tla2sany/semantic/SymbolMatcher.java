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

public interface SymbolMatcher {
	
	/**
	 * @return true if the given {@link SymbolNode} matches this predicate.
	 */
	boolean matches(final SymbolNode aSymbol);

	public static class NameAndTypeMatcher implements SymbolMatcher {
	
		private String prefix;
		
		//** Invoked by clients of ModuleNode#getSymbols **//
		
		public NameAndTypeMatcher setPrefix(final String aPrefix) {
			this.prefix = aPrefix;
			return this;
		}
		
		//** Invoked by ModuleNode, overridden by clients **//
		
		/* (non-Javadoc)
		 * @see tla2sany.semantic.SymbolMatcher#matches(tla2sany.semantic.SymbolNode)
		 */
		@Override
		public boolean matches(final SymbolNode aSymbol) {
			if (!matchesAnyType() && !matchTypes().contains(aSymbol.getClass())) {
				// TODO Better test for isAssignableFrom(aSymbol.getClass()), but would require
				// looping over matchTypes.
				return false;
			}
			if (aSymbol.getKind() == ASTConstants.BuiltInKind && aSymbol.getName().toString().startsWith("$")) {
				// Do not match internal built-in operators.
				return false;
			}

			final String symbolName = aSymbol.getName().toString();
			if (matchCaseSensitive() && !symbolName.startsWith(getPrefix())) {
				return false;
			} else if (!symbolName.toLowerCase().startsWith(getPrefix().toLowerCase())){
				return false;
			}
			
			return true;
		}
		
		//** Invoked by matches, subclasses may override **//
		
		/**
		 * @return A Set of SymbolNodes to match.
		 */
		protected Set<Class<? extends SymbolNode>> matchTypes() {
			return new HashSet<>();
		}
		
		protected boolean matchesAnyType() {
			return matchTypes().isEmpty();
		}
		
		protected boolean matchCaseSensitive() {
			return false;
		}
	
		protected String getPrefix() {
			return prefix;
		}
	}
}
