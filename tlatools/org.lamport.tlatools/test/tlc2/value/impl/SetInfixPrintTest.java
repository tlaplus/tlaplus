/*******************************************************************************
 * Copyright (c) 2026 Oracle and/or its affiliates. All rights reserved.
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
package tlc2.value.impl;

import static org.junit.Assert.assertEquals;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import tlc2.TLCGlobals;

/**
 * Terse printing of lazy {@code \cup}, {@code \cap}, and {@code \} values.
 * With {@code -terse}, TLC leaves these sets unexpanded, and trace exploration
 * copies the printed text into a generated specification.
 */
public class SetInfixPrintTest {

	private boolean expand;

	@Before
	public void disableExpansion() {
		expand = TLCGlobals.expand;
		TLCGlobals.expand = false;
	}

	@After
	public void restoreExpansion() {
		TLCGlobals.expand = expand;
	}

	@Test
	public void subsetCup() {
		assertEquals("SUBSET (({1}) \\cup ({2}))",
				new SubsetValue(new SetCupValue(SetEnumValue.ints(1), SetEnumValue.ints(2))).toString());
	}

	@Test
	public void subsetCap() {
		assertEquals("SUBSET (({1}) \\cap ({2}))",
				new SubsetValue(new SetCapValue(SetEnumValue.ints(1), SetEnumValue.ints(2))).toString());
	}

	@Test
	public void subsetDiff() {
		assertEquals("SUBSET (({0, 1}) \\ ({1}))",
				new SubsetValue(new SetDiffValue(SetEnumValue.ints(0, 1), SetEnumValue.ints(1))).toString());
	}

	@Test
	public void subsetCupOfSubsets() {
		assertEquals("SUBSET ((SUBSET {1}) \\cup (SUBSET {2}))",
				new SubsetValue(new SetCupValue(SubsetValue.subset(1), SubsetValue.subset(2))).toString());
	}

	@Test
	public void cupSubsetSubset() {
		assertEquals("(SUBSET {0, 1}) \\cup (SUBSET {2})",
				new SetCupValue(SubsetValue.subset(0, 1), SubsetValue.subset(2)).toString());
	}

	@Test
	public void capSubsetSubset() {
		assertEquals("(SUBSET {0, 1}) \\cap (SUBSET {1, 2})",
				new SetCapValue(SubsetValue.subset(0, 1), SubsetValue.subset(1, 2)).toString());
	}

	@Test
	public void diffSubsetSubset() {
		assertEquals("(SUBSET {0, 1}) \\ (SUBSET {1})",
				new SetDiffValue(SubsetValue.subset(0, 1), SubsetValue.subset(1)).toString());
	}

	@Test
	public void cupUnionSubset() {
		assertEquals("(UNION({{0}, {1}})) \\cup (SUBSET {2})",
				new SetCupValue(UnionValue.union(0, 1), SubsetValue.subset(2)).toString());
	}

	@Test
	public void capSubsetUnion() {
		assertEquals("(SUBSET {0, 1}) \\cap (UNION({{0}, {1}}))",
				new SetCapValue(SubsetValue.subset(0, 1), UnionValue.union(0, 1)).toString());
	}

	@Test
	public void diffUnionSubset() {
		assertEquals("(UNION({{0}, {1}})) \\ (SUBSET {1})",
				new SetDiffValue(UnionValue.union(0, 1), SubsetValue.subset(1)).toString());
	}

	@Test
	public void cupSubsetSet() {
		assertEquals("(SUBSET {0, 1}) \\cup ({2})",
				new SetCupValue(SubsetValue.subset(0, 1), SetEnumValue.ints(2)).toString());
	}

	@Test
	public void diffSetSubset() {
		assertEquals("({0, 1}) \\ (SUBSET {1})",
				new SetDiffValue(SetEnumValue.ints(0, 1), SubsetValue.subset(1)).toString());
	}

	@Test
	public void cupIntervalSubsets() {
		assertEquals("(SUBSET (1..3)) \\cup (SUBSET (4..5))",
				new SetCupValue(new SubsetValue(new IntervalValue(1, 3)), new SubsetValue(new IntervalValue(4, 5)))
						.toString());
	}

	@Test
	public void cupSubsetChain() {
		final Value subset01 = SubsetValue.subset(0, 1);
		final Value subset2 = SubsetValue.subset(2);
		assertEquals("((SUBSET {0, 1}) \\cup (SUBSET {2})) \\cup (SUBSET {1})",
				new SetCupValue(new SetCupValue(subset01, subset2), SubsetValue.subset(1)).toString());
	}

	@Test
	public void cupOfCap() {
		assertEquals("(({1}) \\cap ({2})) \\cup ({3})",
				new SetCupValue(new SetCapValue(SetEnumValue.ints(1), SetEnumValue.ints(2)), SetEnumValue.ints(3))
						.toString());
	}

	@Test
	public void cupThenCap() {
		assertEquals("({1}) \\cup (({2}) \\cap ({3}))",
				new SetCupValue(SetEnumValue.ints(1), new SetCapValue(SetEnumValue.ints(2), SetEnumValue.ints(3)))
						.toString());
	}

	@Test
	public void capOfCup() {
		assertEquals("(({1}) \\cup ({2})) \\cap ({3})",
				new SetCapValue(new SetCupValue(SetEnumValue.ints(1), SetEnumValue.ints(2)), SetEnumValue.ints(3))
						.toString());
	}

	@Test
	public void capThenCup() {
		assertEquals("({1}) \\cap (({2}) \\cup ({3}))",
				new SetCapValue(SetEnumValue.ints(1), new SetCupValue(SetEnumValue.ints(2), SetEnumValue.ints(3)))
						.toString());
	}

	@Test
	public void diffOfDiff() {
		assertEquals("(({0, 1}) \\ ({1})) \\ ({0})",
				new SetDiffValue(new SetDiffValue(SetEnumValue.ints(0, 1), SetEnumValue.ints(1)), SetEnumValue.ints(0))
						.toString());
	}

	@Test
	public void diffThenDiff() {
		assertEquals("({0, 1}) \\ (({1}) \\ ({0}))",
				new SetDiffValue(SetEnumValue.ints(0, 1), new SetDiffValue(SetEnumValue.ints(1), SetEnumValue.ints(0)))
						.toString());
	}

	@Test
	public void cupOfDiff() {
		assertEquals("(({0, 1}) \\ ({1})) \\cup ({0})",
				new SetCupValue(new SetDiffValue(SetEnumValue.ints(0, 1), SetEnumValue.ints(1)), SetEnumValue.ints(0))
						.toString());
	}

	@Test
	public void diffOfCup() {
		assertEquals("({0, 1}) \\ (({1}) \\cup ({0}))",
				new SetDiffValue(SetEnumValue.ints(0, 1), new SetCupValue(SetEnumValue.ints(1), SetEnumValue.ints(0)))
						.toString());
	}

	@Test
	public void capOfDiff() {
		assertEquals("(({0, 1}) \\ ({1})) \\cap ({0})",
				new SetCapValue(new SetDiffValue(SetEnumValue.ints(0, 1), SetEnumValue.ints(1)), SetEnumValue.ints(0))
						.toString());
	}

	@Test
	public void diffOfCap() {
		assertEquals("({0, 1}) \\ (({1}) \\cap ({0}))",
				new SetDiffValue(SetEnumValue.ints(0, 1), new SetCapValue(SetEnumValue.ints(1), SetEnumValue.ints(0)))
						.toString());
	}

	@Test
	public void cupSetSet() {
		assertEquals("({0, 1}) \\cup ({2})", new SetCupValue(SetEnumValue.ints(0, 1), SetEnumValue.ints(2)).toString());
	}

	@Test
	public void cupKSubsetSet() {
		assertEquals("({s \\in SUBSET (1..3) : Cardinality(s) = 1}) \\cup ({0})",
				new SetCupValue(new KSubsetValue(1, new IntervalValue(1, 3)), SetEnumValue.ints(0)).toString());
	}
}
