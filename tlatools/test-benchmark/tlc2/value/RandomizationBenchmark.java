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
package tlc2.value;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.BenchmarkMode;
import org.openjdk.jmh.annotations.Measurement;
import org.openjdk.jmh.annotations.Mode;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.State;
import org.openjdk.jmh.annotations.Warmup;

import tlc2.util.FP64;

@State(Scope.Benchmark)
public class RandomizationBenchmark {

	private static final Enumerable enum016;
	private static final Enumerable enum032;
	private static final Enumerable enum064;
	private static final Enumerable enum128;
	private static final Enumerable enum256;
	private static final Enumerable enum512;

	private static final int twoPow24 = (int) (Math.pow(2, 24) - 1);
	private static final int twoPow20 = (int) (Math.pow(2, 20) - 1);
	private static final int twoPow16 = (int) (Math.pow(2, 16) - 1);
	private static final Enumerable fcns008x008;
	private static final Enumerable fcns016x008;
	private static final Enumerable fcns016x016;
	private static final Enumerable fcns032x016;
	private static final Enumerable fcns032x032;

	private static ValueVec getValues(int from, int to) {
		final ValueVec vec = new ValueVec(to - from);
		for (int i = from; i <= to; i++) {
			vec.addElement(IntValue.gen(i));
		}
		return vec;
	}

	static {
		EnumerableValue.setRandom(15041980L);
		EnumerableValue.resetRandom();

		FP64.Init();

		enum016 = new SetEnumValue(getValues(1, 16), true);
		enum032 = new SetEnumValue(getValues(1, 32), true);
		enum064 = new SetEnumValue(getValues(1, 64), true);
		enum128 = new SetEnumValue(getValues(1, 128), true);
		enum256 = new SetEnumValue(getValues(1, 256), true);
		enum512 = new SetEnumValue(getValues(1, 512), true);

		fcns008x008 = new SetOfFcnsValue(new SetEnumValue(getValues(1, 8), true),
				new SetEnumValue(getValues(1, 8), true));
		fcns016x008 = new SetOfFcnsValue(new SetEnumValue(getValues(1, 16), true),
				new SetEnumValue(getValues(1, 8), true));
		fcns016x016 = new SetOfFcnsValue(new SetEnumValue(getValues(1, 16), true),
				new SetEnumValue(getValues(1, 16), true));
		fcns032x016 = new SetOfFcnsValue(new SetEnumValue(getValues(1, 32), true),
				new SetEnumValue(getValues(1, 16), true));
		fcns032x032 = new SetOfFcnsValue(new SetEnumValue(getValues(1, 32), true),
				new SetEnumValue(getValues(1, 32), true));
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubset016() {
		return enum016.getRandomSubset(enum016.size() - 1);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubset032() {
		return enum032.getRandomSubset(enum032.size() - 1);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubset064() {
		return enum064.getRandomSubset(enum064.size() - 1);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubset128() {
		return enum128.getRandomSubset(enum128.size() - 1);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubset256() {
		return enum256.getRandomSubset(enum256.size() - 1);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubset512() {
		return enum512.getRandomSubset(enum512.size() - 1);
	}

	/* randomSubset with SetOfFcns */

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns008x008p16() {
		return fcns008x008.getRandomSubset(twoPow16);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns008x008p20() {
		return fcns008x008.getRandomSubset(twoPow20);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns008x008p24() {
		return fcns008x008.getRandomSubset(twoPow24);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns016x008p16() {
		return fcns016x008.getRandomSubset(twoPow16);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns016x008p20() {
		return fcns016x008.getRandomSubset(twoPow20);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns016x008p24() {
		return fcns016x008.getRandomSubset(twoPow24);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns016x016p16() {
		return fcns016x016.getRandomSubset(twoPow16);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns016x016p20() {
		return fcns016x016.getRandomSubset(twoPow20);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns016x016p24() {
		return fcns016x016.getRandomSubset(twoPow24);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns032x016p16() {
		return fcns032x016.getRandomSubset(twoPow16);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns032x016p20() {
		return fcns032x016.getRandomSubset(twoPow20);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns032x016p24() {
		return fcns032x016.getRandomSubset(twoPow24);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns032x032p16() {
		return fcns032x032.getRandomSubset(twoPow16);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns032x032p20() {
		return fcns032x032.getRandomSubset(twoPow20);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue randomSubsetFcns032x032p24() {
		return fcns032x032.getRandomSubset(twoPow24);
	}
}
