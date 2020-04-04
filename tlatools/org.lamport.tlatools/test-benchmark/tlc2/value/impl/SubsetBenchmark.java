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
import org.openjdk.jmh.annotations.Level;
import org.openjdk.jmh.annotations.Param;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.State;

import tlc2.util.FP64;
import tlc2.value.RandomEnumerableValues;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.IntervalValue;
import tlc2.value.impl.SubsetValue;

@State(Scope.Benchmark)
public class SubsetBenchmark {

	static {
		RandomEnumerableValues.setSeed(15041980L);
		RandomEnumerableValues.reset();

		FP64.Init();
	}
	
	@Param({"10", "12", "14", "16", "20", "24"})
	public int numOfElements;
	
	@Param({"32", "64", "128", "256"})
	public int size;

	public SubsetValue subset;
		
	@Setup(Level.Invocation)
	public void setup() {
		if (size < 128 || (size >= 128 && numOfElements <= 20)) {
			subset = (SubsetValue) new SubsetValue(new IntervalValue(1, size)).normalize();
		} else {
			// This appears to be the only way to skip permutations from the parameter space
			// size X numOfElements. These permutations will go OOM or reach GC overhad
			// limit anyway.
			System.exit(0);
		}
	}

	@Benchmark
	public Enumerable randomSetOfSubsets() {
		return subset.getRandomSetOfSubsets(1 << numOfElements, .1d);
	}

	@Benchmark
	public Enumerable randomSetOfSubsetsExact() {
		return subset.getRandomSetOfSubsets(1 << numOfElements, 10);
	}
}
