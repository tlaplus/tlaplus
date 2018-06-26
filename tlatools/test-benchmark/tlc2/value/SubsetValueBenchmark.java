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
public class SubsetValueBenchmark {

	private static final SubsetValue subset35;
	private static final SubsetValue subset60;
	private static final SubsetValue subset100;
	private static final SubsetValue subset200;
	private static final SubsetValue subset300;
	private static final SubsetValue subset400;

	private static final int k = 80000;
	private static final double d = 0.1d;
	private static final int k2 = 160000;
	private static final double d2 = 0.2d;

	static {
		EnumerableValue.setRandom(15041980L);
		EnumerableValue.resetRandom();

		FP64.Init();

		subset35 = new SubsetValue(new IntervalValue(1, 35));
		subset35.normalize();
		subset60 = new SubsetValue(new IntervalValue(1, 60));
		subset60.normalize();
		subset100 = new SubsetValue(new IntervalValue(1, 100));
		subset100.normalize();
		subset200 = new SubsetValue(new IntervalValue(1, 200));
		subset200.normalize();
		subset300 = new SubsetValue(new IntervalValue(1, 300));
		subset300.normalize();
		subset400 = new SubsetValue(new IntervalValue(1, 400));
		subset400.normalize();
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN035k80d01() {
		return subset35.getRandomSetOfSubsets(k, d);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN060k80d01() {
		return subset60.getRandomSetOfSubsets(k, d);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN100k80d01() {
		return subset100.getRandomSetOfSubsets(k, d);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN200k80d01() {
		return subset200.getRandomSetOfSubsets(k, d);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN300k80d01() {
		return subset300.getRandomSetOfSubsets(k, d);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN400k80d01() {
		return subset400.getRandomSetOfSubsets(k, d);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN035k16d01() {
		return subset35.getRandomSetOfSubsets(k2, d);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN060k16d01() {
		return subset60.getRandomSetOfSubsets(k2, d);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN100k16d01() {
		return subset100.getRandomSetOfSubsets(k2, d);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN200k16d01() {
		return subset200.getRandomSetOfSubsets(k2, d);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN300k16d01() {
		return subset300.getRandomSetOfSubsets(k2, d);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN400k16d01() {
		return subset400.getRandomSetOfSubsets(k2, d);
	}
	
	/* d2 */

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN035k80d02() {
		return subset35.getRandomSetOfSubsets(k, d2);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN060k80d02() {
		return subset60.getRandomSetOfSubsets(k, d2);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN100k80d02() {
		return subset100.getRandomSetOfSubsets(k, d2);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN200k80d02() {
		return subset200.getRandomSetOfSubsets(k, d2);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN300k80d02() {
		return subset300.getRandomSetOfSubsets(k, d2);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN400k80d02() {
		return subset400.getRandomSetOfSubsets(k, d2);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN035k16d02() {
		return subset35.getRandomSetOfSubsets(k2, d2);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN060k16d02() {
		return subset60.getRandomSetOfSubsets(k2, d2);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN100k16d02() {
		return subset100.getRandomSetOfSubsets(k2, d2);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN200k16d02() {
		return subset200.getRandomSetOfSubsets(k2, d2);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN300k16d02() {
		return subset300.getRandomSetOfSubsets(k2, d2);
	}

	@Benchmark
	@Warmup(iterations = 3, time = 1)
	@Measurement(iterations = 3, time = 1)
	@BenchmarkMode(Mode.Throughput)
	public EnumerableValue probabilisticN400k16d02() {
		return subset400.getRandomSetOfSubsets(k2, d2);
	}
}

/*
 * Mode.Throughput: Calculate number of operations in a time unit. (Higher score
 * better) Mode.AverageTime: Calculate an average running time. (Lower score
 * better) Mode.SampleTime: Calculate how long does it take for a method to run
 * (including percentiles). Mode.SingleShotTime: Just run a method once (useful
 * for cold-testing mode). Or more than once if you have specified a batch size
 * for your iterations (see @Measurement annotation below) – in this case JMH
 * will calculate the batch running time (total time for all invocations in a
 * batch). Any set of these modes You can specify any set of these modes – the
 * test will be run several times (depending on number of requested modes).
 * Mode.All: All these modes one after another.
 */