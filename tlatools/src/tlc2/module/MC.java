/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved. 
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
package tlc2.module;

import tlc2.value.Value;

/*
 * The Toolbox generates an MC.tla file upon TLC startup which extends the actual
 * specification being verified. Additionally, to evaluate any constant expression,
 * MC.tla also extends TLC.tla to use the PrintT operator defined in TLC.tla 
 * (and its module override tlc2.module.TLC):
 * "ASSUME PrintT(...)"
 * 
 * Extending TLC.tla in MC.tla can cause a name clash if the actual specification
 * does *not* extend TLC and happens to declare an operator colliding with one 
 * in TLC.tla (e.g. "Permutations", "SortSeq", ...).
 * 
 * To resolve this name clash, the Toolbox no longer extends TLC.tla in MC.tla but
 * instead generates a LOCAL declaration of PrintT its name prefixed with MC:
 * "LOCAL MCPrintT(out) == TRUE
 *  ASSUME MCPrintT(...)"
 * 
 * TLC.tla's PrintT is override by the tlc2.module.TLC#MCPrintT module override.
 * Thus, the LOCAL construct above only resolves the name clash at the SANY level,
 * but produces no output. This class effectively associates MC.tla's MCPrintT with
 * tlc2.module.TLC#PrintT.
 * 
 * The same is done for tlc2.module.TLC#Permutations, required if a constant is declared
 * to be a symmetry set.
 * 
 * @see org.lamport.tla.toolbox.tool.tlc.model.ModelWriter.addConstantExpressionEvaluation(String, String)
 */
public class MC {

	public static final long serialVersionUID = 20171127L;

	/**
	 * @see TLC#PrintT(Value)
	 */
	public static Value MCPrintT(Value v1) {
		return TLC.PrintT(v1);
	}
	
	// For symmetry reasons also support Print (would be confusing if eval
	// expression support PrintT but not Print).
	/**
	 * @see TLC#Print(Value, Value)
	 */
	public static Value MCPrint(Value v1, Value v2) {
		return TLC.Print(v1, v2);
	}
	
	/**
	 * @see TLC#Permutations(Value)
	 */
	public static Value MCPermutations(Value s) {
		return TLC.Permutations(s);
	}
}
