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

@State(Scope.Benchmark)
public class SetOfFcnsBenchmark {

	static {
		RandomEnumerableValues.setSeed(15041980L);
		RandomEnumerableValues.reset();

		FP64.Init();
	}
	
	@Param({"10", "12", "14", "16"})
	public int numOfElements;
	
	@Param({"16", "32", "46"})
	public int sizeT;
	
	@Param({"8", "16", "46"})
	public int sizeS;

	// 08x16 ~= 2^32 = 4294967296
	// 16x16 = 2^64  = 10^19
	// 16x32 ~= 2^128 ~= 10^38
	// 46x46 ~= 2^256 ~= 10^77
	
	public Enumerable setOfFcns;
		
	@Setup(Level.Invocation)
	public void setup() {
		if ((sizeS == 8 && sizeT == 16)
				|| (sizeS == 16 && sizeT == 16)
				|| (sizeS == 16 && sizeT == 32)
				|| (sizeS == 46 && sizeT == 46)) {
			final Value domain = new IntervalValue(1, sizeS);
			final Value range = new IntervalValue(1, sizeT);
			setOfFcns = (Enumerable) new SetOfFcnsValue(domain, range).normalize();
		} else {
			// This appears to be the only way to skip permutations from the parameter space
			// sizeS X sizeT X numOfElements.
			System.exit(0);
		}
	}

	@Benchmark
	public Enumerable randomSubset() {
		return setOfFcns.getRandomSubset(1 << numOfElements);
	}
}
