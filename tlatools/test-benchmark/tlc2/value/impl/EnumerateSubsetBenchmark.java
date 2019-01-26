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
package tlc2.value.impl;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.Param;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.State;

import tlc2.util.FP64;
import tlc2.value.RandomEnumerableValues;

@State(Scope.Benchmark)
public class EnumerateSubsetBenchmark {

	static {
		RandomEnumerableValues.setSeed(15041980L);
		RandomEnumerableValues.reset();

		FP64.Init();
	}
	
	@Param({"0", "1", "2", "3", "4", "8", "10", "12", "14", "16", "18", "19"})
	public int numOfElements;

	@Benchmark
	public Enumerable elementsAlwaysNormalized() {
		final IntervalValue inner = new IntervalValue(1, numOfElements);
		final SubsetValue subset = new SubsetValue(inner);

		final ValueVec vals = new ValueVec(subset.size());
		final ValueEnumeration Enum = subset.elementsNormalized();
		Value  elem;
		while ((elem = Enum.nextElement()) != null) {
			vals.addElement(elem);
		}
        return (Enumerable) new SetEnumValue(vals, true).normalize();
	}

	@Benchmark
	public Enumerable kElementsNotNormalized() {
		final IntervalValue inner = new IntervalValue(1, numOfElements);
		final SubsetValue subset = new SubsetValue(inner);

		final ValueVec vec = new ValueVec(subset.size());
		for (int i = 0; i <= inner.size(); i++) {
			final ValueEnumeration Enum = subset.kElements(i);
			Value  elem;
			while ((elem = Enum.nextElement()) != null) {
				vec.addElement(elem);
			}
		}
        return (Enumerable) new SetEnumValue(vec, false);
	}
	
	@Benchmark
	public Enumerable kElementsNormalized() {
		final IntervalValue inner = new IntervalValue(1, numOfElements);
		final SubsetValue subset = new SubsetValue(inner);

		final ValueVec vec = new ValueVec(subset.size());
		for (int i = 0; i <= inner.size(); i++) {
			final ValueEnumeration Enum = subset.kElements(i);
			Value  elem;
			while ((elem = Enum.nextElement()) != null) {
				vec.addElement(elem);
			}
		}
        return (Enumerable) new SetEnumValue(vec, false).normalize();
	}

	@Benchmark
	public Enumerable elementsNotNormalized() {
		final IntervalValue inner = new IntervalValue(1, numOfElements);
		final SubsetValue subset = new SubsetValue(inner);
		
		final ValueVec vals = new ValueVec(subset.size());
		final ValueEnumeration Enum = subset.elementsLexicographic();
		Value  elem;
		while ((elem = Enum.nextElement()) != null) {
			vals.addElement(elem);
		}
		return (Enumerable) new SetEnumValue(vals, false);
	}

	@Benchmark
	public Enumerable elementsNormalized() {
		final IntervalValue inner = new IntervalValue(1, numOfElements);
		final SubsetValue subset = new SubsetValue(inner);
		
		final ValueVec vals = new ValueVec(subset.size());
		final ValueEnumeration Enum = subset.elementsLexicographic();
		Value  elem;
		while ((elem = Enum.nextElement()) != null) {
			vals.addElement(elem);
		}
		return (Enumerable) new SetEnumValue(vals, false).normalize();
	}
}
