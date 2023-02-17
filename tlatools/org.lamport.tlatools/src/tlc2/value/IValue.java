/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
 * Copyright (c) 2023, Oracle and/or its affiliates.
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

/**
 * A value is a simplified TLA+ term.  Values fall into one of several key categories:
 * <ul>
 *     <li>Atomic values like {@link BoolValue}, {@link IntValue}, and {@link ModelValue}</li>
 *     <li>Composite values like {@link tlc2.value.impl.SetEnumValue} and {@link tlc2.value.impl.FcnRcdValue} that
 *         build larger structures out of other values</li>
 *     <li>Lazy values like {@link tlc2.value.impl.LazyValue}, {@link tlc2.value.impl.SubsetValue}, and
 *         {@link tlc2.value.impl.FcnLambdaValue} that delay full simplification until the last possible moment</li>
 *     <li>Special values like {@link tlc2.value.impl.OpRcdValue} and {@link tlc2.value.impl.UserValue} whose
 *         purposes are highly varied</li>
 * </ul>
 *
 * <h2>Comparability</h2>
 * In TLA+, expressions like <code>"a" = 1</code> are definitely either true or false.  However, the axioms of TLA+ do
 * not define which!  Therefore, it would be incorrect for TLC to return a definitive result for such comparisons.
 * While TLC values implement {@link #equals(Object)} and {@link #compareTo(Object)}, comparisons between certain kinds
 * of values will conservatively throw an exception instead of returning a result.
 *
 * <p>These exceptions should not be taken as evidence that the values are not equal!  Again, <code>"a" = 1</code>
 * is either true or false, but we can't know which it is.
 *
 * <h2>Mutability and Lifecycle</h2>
 * Value objects are logically immutable: the value they represent never changes.
 *
 * <p>Many implementations of this interface have a dynamic representation.  That means that while the value they
 * represent will never change, the actual bytes in memory CAN and DO change to dynamically optimize for certain kinds
 * of operations.  For example, in {@link tlc2.value.impl.SetEnumValue}, the array <code>[2, 2, 1]</code> represents
 * the set <code>{1, 2}</code>.  However, when the value is normalized ({@link #deepNormalize()}), the array will be
 * sorted and deduplicated to produce <code>[1, 2]</code>.  That array still represents the set <code>{1, 2}</code>,
 * but it has been rearranged to enable binary search.
 *
 * <p>Dynamic representations are in tension with TLC's high-performance multithreading goals, since multiple threads
 * may read and write the same value concurrently, leading to race conditions.  To reduce the overhead of using values,
 * the value classes generally do not use locks or volatile fields.  Instead, they have a lifecycle that must be
 * strictly obeyed:
 *
 * <pre>
 *     NEW ==> NORMALIZED ==> FINGERPRINTED
 * </pre>
 *
 * A value can only be shared among threads once it is fingerprinted.  At that point, the value MUST have a static
 * representation that never changes to avoid race conditions.
 *
 * <p>Values are normalized using {@link #deepNormalize()} or {@link tlc2.value.impl.Value#normalize()} and they are
 * fingerprinted using {@link #fingerPrint(long)} or {@link #initialize()}.
 *
 * <h2>Operators and Arity</h2>
 * In TLA+, operators can be passed to other operators.  For instance, the operator <code>F(G(_), _) == ...</code>
 * takes a unary operator <code>G</code> as an argument.  As a result, TLC values have to be able to represent
 * operators like <code>G</code>.
 *
 * <p>Values with nonzero arity extend {@link tlc2.value.impl.OpValue}, and the
 * {@link tlc2.value.impl.OpValue#eval} method applies an operator to arguments.
 *
 * <h2>Expression Levels</h2>
 * Some value types like {@link tlc2.value.impl.LazyValue} and {@link tlc2.value.impl.OpLambdaValue} wrap TLA+
 * expressions.  They may even wrap expressions with non-constant level (see {@link tla2sany.semantic.LevelConstants}).
 * As such, the meaning of a value is not necessarily fixed and may depend on the current behavior or whether the value
 * is used inside <code>ENABLED</code>.
 */
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