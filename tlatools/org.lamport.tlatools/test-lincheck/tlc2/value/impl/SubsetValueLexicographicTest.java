/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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

import org.jetbrains.lincheck.datastructures.Operation;
import org.junit.Test;

/**
 * The set SUBSET ({3} \cup {1, 2}). Two workers that enumerate its subsets in
 * lexicographic order must both get them in the order of the sorted elements
 * 1, 2, 3. The enumerator converts the union to a set of the unsorted elements
 * 3, 1, 2, writes that set to the outer SubsetValue, sorts the set it reads
 * back, and then reads the outer SubsetValue again for the elements. If the
 * other worker overwrites the outer SubsetValue in between with its own set,
 * which it has not sorted yet, the first worker enumerates in the order 3, 1, 2.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/1445
 */
public class SubsetValueLexicographicTest extends ValueLincheckTestCase {

	private final SubsetValue subset;

	public SubsetValueLexicographicTest() {
		this(new SubsetValue(new SetCupValue(new SetEnumValue(new Value[] { IntValue.gen(3) }, true),
				new SetEnumValue(new Value[] { IntValue.gen(1), IntValue.gen(2) }, true))));
	}

	private SubsetValueLexicographicTest(final SubsetValue subset) {
		super(subset);
		this.subset = subset;
	}

	@Operation
	public String elementsLexicographic() {
		final StringBuilder sb = new StringBuilder();
		final ValueEnumeration elements = subset.elementsLexicographic();
		Value v;
		while ((v = elements.nextElement()) != null) {
			sb.append(v);
		}
		return sb.toString();
	}

	@Test
	public void elementsLexicographicAndElementsLexicographic() {
		modelCheckingParallel("elementsLexicographic", "elementsLexicographic");
	}
}
