/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
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

package tlc2.tool.liveness;

import java.io.IOException;

import tlc2.tool.TLCState;
import tlc2.util.BitVector;
import tlc2.util.SetOfStates;

public interface ILiveChecker {

	/**
	 * This method records that state is an initial state in the behavior graph.
	 * It is called when a new initial state is generated.
	 */
	void addInitState(TLCState state, long stateFP);

	/**
	 * This method adds new nodes into the behavior graph induced by s0. It is
	 * called after the successors of s0 are computed.
	 */
	void addNextState(TLCState s0, long fp0, SetOfStates nextStates, BitVector checkActionResults,
			boolean[] checkStateResults) throws IOException;

	AbstractDiskGraph getDiskGraph();

	OrderOfSolution getSolution();

}