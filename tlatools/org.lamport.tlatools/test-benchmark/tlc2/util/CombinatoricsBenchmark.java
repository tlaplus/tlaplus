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
package tlc2.util;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.BenchmarkMode;
import org.openjdk.jmh.annotations.Measurement;
import org.openjdk.jmh.annotations.Mode;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.State;
import org.openjdk.jmh.annotations.Warmup;

@State(Scope.Benchmark)
public class CombinatoricsBenchmark {
	
	private static List<BigInteger> bincoef;
	private static List<BigInteger> slowBincoef;

	static {
		bincoef = new ArrayList<BigInteger>(187489);
		slowBincoef = new ArrayList<BigInteger>(187489);
	}
	
	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public List<BigInteger> bigChoose() {
		for (int n = Combinatorics.MAXCHOOSENUM + 1; n < Combinatorics.MAXCHOOSENUM << 3; n++) {
			for (int k = Combinatorics.MAXCHOOSENUM + 1; k < Combinatorics.MAXCHOOSENUM << 3; k++) {
				bincoef.add(Combinatorics.bigChoose(n, k));
			}
		}
		return bincoef;
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public List<BigInteger> slowBigChoose() {
		for (int n = Combinatorics.MAXCHOOSENUM + 1; n < Combinatorics.MAXCHOOSENUM << 3; n++) {
			for (int k = Combinatorics.MAXCHOOSENUM + 1; k < Combinatorics.MAXCHOOSENUM << 3; k++) {
				slowBincoef.add(Combinatorics.slowBigChoose(n, k));
			}
		}
		return slowBincoef;
	}
}
