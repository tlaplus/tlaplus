/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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
package tlc2.tool;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.OpDeclNode;
import tlc2.value.impl.IntValue;
import util.UniqueString;

public abstract class TLCStates {

	public static TLCState createDummyState() {
		return createDummyState(1);
	}

	public static TLCState createDummyState(final int numVars) {
		UniqueString.setVariableCount(numVars);

		// Create variable declarations (no values yet).
		final OpDeclNode[] variables = new OpDeclNode[numVars];
		for (int i = 0; i < numVars; i++) {
			UniqueString us = UniqueString.uniqueStringOf("v" + Integer.toString(i));
			us.setLoc(i);
			variables[i] = new OpDeclNode(us, ASTConstants.VariableDeclKind, 1, 0, null, null, null);
		}

		// Initialize the empty state (variable declarations are static/final per TLC
		// run).
		TLCStateMut.setVariables(variables);
		final TLCState state = TLCState.Empty.createEmpty();
		state.uid = 0;

		// Assign values to variables.
		for (int i = 0; i < numVars; i++) {
			state.bind(variables[i].getName(), IntValue.gen(i));
		}

		return state;
	}
}
