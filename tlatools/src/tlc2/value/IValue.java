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

import tla2sany.semantic.SemanticNode;
import tlc2.tool.coverage.CostModel;

public interface IValue {

	/**
	   * This method returns the value kind: an integer that represents
	   * the kind of this value. See the interface ValueConstants.java.
	   */
	byte getKind();

	String getKindString();

	/* This method compares this with val.  */
	int compareTo(Object val);

	/* This method returns true iff elem is a member of this. */
	boolean member(IValue elem);

	/* This method returns a new value after taking the except. */
	IValue takeExcept(ValueExcept ex);

	/* This method returns a new value after taking the excepts. */
	IValue takeExcept(ValueExcept[] exs);

	void write(ValueOutputStream vos) throws IOException;

	IValue setCostModel(CostModel cm);

	CostModel getCostModel();

	void setSource(SemanticNode semanticNode);

	SemanticNode getSource();

	boolean hasSource();

	/**
	   * This method normalizes (destructively) the representation of
	   * the value. It is essential for equality comparison.
	   */
	boolean isNormalized();

	IValue normalize();

	boolean isEmpty();

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

	/* This method returns true iff val can be assigned to this. */
	boolean assignable(IValue val);

	/* This method returns the hash code of this value. */
	int hashCode();

	/**
	   * This method selects the component of this value. The component is
	   * specified by path.
	   */
	IValue select(IValue[] path);

	/* Convert val into a SetEnumValue.  Returns null if not possible. */
	IValue toSetEnum();

	/*
	   * This method converts a value to a function value. It returns
	   * null if the conversion fails.
	   */
	IValue toFcnRcd();

	/*
	   * This method converts a value to a function value. It returns
	   * null if the conversion fails.
	   */
	IValue toRcd();

	/*
	   * This method converts a value to a tuple value. It returns
	   * null if the conversion fails.
	   */
	IValue toTuple();

	/**
	   * This abstract method returns a string representation of this
	   * value. Each subclass must provide its own implementation.
	   */
	StringBuffer toString(StringBuffer sb, int offset);

	/* The string representation of this value */
	String toString();

	String toString(String delim);

}