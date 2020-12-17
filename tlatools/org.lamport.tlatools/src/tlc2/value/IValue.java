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
package tlc2.value;

import java.io.IOException;
import java.util.Random;

import tla2sany.semantic.SemanticNode;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.TLCVariable;

public interface IValue extends Comparable<Object> {

	/* This method compares this with val.  */
	@Override
	int compareTo(Object val);

	void write(IValueOutputStream vos) throws IOException;

	IValue setCostModel(CostModel cm);

	CostModel getCostModel();

	void setSource(SemanticNode semanticNode);

	SemanticNode getSource();

	boolean hasSource();

	/* MAK 09/17/2019: Introduced to guarantee that Value instances are
	 * fully initialized when created by the SpecProcessor (as opposed
	 * to by workers during state space exploration).
	 */
	/**
	 * Fully initialize this instance which includes:
	 * - deep normalization
	 * - conversion and caching iff defined by the sub-class
	 * 
	 *  No further mutation of this instance should be required
	 *  for any evaluation whatsoever.
	 *  
	 *  Afterwards, isNormalized below returns true (it does not
	 *  return true for all sub-classes when only deepNormalized
	 *  is executed)!
	 *  
	 *  see comment in UnionValue#deepNormalize too
	 */
	default IValue initialize() {
		this.deepNormalize();
		// Execute fingerprint code path to internally trigger convertAndCache iff
		// defined (0L parameter is not relevant)
		this.fingerPrint(0L);
		return this;
	}
	
	/**
	   * This method normalizes (destructively) the representation of
	   * the value. It is essential for equality comparison.
	   */
	boolean isNormalized();

	/* Fully normalize this (composite) value. */
	void deepNormalize();

	/* This method returns the fingerprint of this value. */
	long fingerPrint(long fp);

	/**
	   * This method returns the value permuted by the permutation. It
	   * returns this if nothing is permuted.
	   */
	IValue permute(IMVPerm perm);

	/* This method returns true iff the value is finite. */
	boolean isFinite();

	/* This method returns the size of the value.  */
	int size();

	/* This method returns true iff the value is fully defined. */
	boolean isDefined();

	/* This method makes a real deep copy of this.  */
	IValue deepCopy();

	/**
	   * This abstract method returns a string representation of this
	   * value. Each subclass must provide its own implementation.
	   */
	StringBuffer toString(StringBuffer sb, int offset, boolean swallow);

	/* The string representation of this value */
	String toString();

	String toString(String delim);
	
	String toUnquotedString();

	default boolean isAtom() {
		if (this instanceof ModelValue || this instanceof IntValue || this instanceof StringValue
				|| this instanceof BoolValue) {
			return true;
		}
		return false;
	}
	
	/**
	 * @return true if a value mutates as part of normalization or fingerprinting.
	 */
	default boolean mutates() {
		return true;
	}

	TLCState toState();

	TLCVariable toTLCVariable(TLCVariable variable, Random rnd);
}