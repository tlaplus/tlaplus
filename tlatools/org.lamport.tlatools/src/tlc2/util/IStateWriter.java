/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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
package tlc2.util;

import java.io.IOException;

import tla2sany.semantic.SemanticNode;
import tlc2.tool.Action;
import tlc2.tool.TLCState;

public interface IStateWriter {
	
	public enum Visualization {
		/**
		 * If successor and the current state are identical and the transition
		 * is due to stuttering.
		 */
		STUTTERING,
		/**
		 * No extra visualization hint is given.
		 */
		DEFAULT,
		/**
		 * A dotted line.
		 */
		DOTTED;
	}
	
	public static final short IsNotInModel = 1 << 1;
	public static final short IsUnseen = 0;
	public static final short IsSeen = 1;
	
	default boolean isSet(int v, int control) {
		return (v & control) == control;
	}

	void writeState(TLCState state);

	void writeState(TLCState state, TLCState successor, short stateFlags);
	
	void writeState(TLCState state, TLCState successor, short stateFlags, Action action);

	void writeState(TLCState state, TLCState successor, short stateFlags, Action action, SemanticNode pred);

	void writeState(TLCState state, TLCState successor, short stateFlags, Visualization visualization);
	
	void writeState(TLCState state, TLCState successor, BitVector actionChecks, int from, int length, short stateFlags);

	void writeState(TLCState state, TLCState successor, BitVector actionChecks, int from, int length, short stateFlags, Visualization visualization);
	
	void close();

	String getDumpFileName();

	boolean isNoop();
	
	boolean isDot();
	
	boolean isConstrained();

	void snapshot() throws IOException;
}