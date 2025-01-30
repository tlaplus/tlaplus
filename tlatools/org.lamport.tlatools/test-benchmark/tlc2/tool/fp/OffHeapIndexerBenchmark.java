/*******************************************************************************
 * Copyright (c) 2025 Microsoft Corp. All rights reserved.
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
package tlc2.tool.fp;

import java.io.IOException;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.Level;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.State;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import tlc2.util.RandomGenerator;

@State(Scope.Benchmark)
public class OffHeapIndexerBenchmark {

	RandomGenerator rng = new RandomGenerator(0);
	long seed = 0;

	private OffHeapDiskFPSet.Indexer infinite = new OffHeapDiskFPSet.InfinitePrecisionIndexer(1L << 30, 1);
	private OffHeapDiskFPSet.Indexer infMult = new OffHeapDiskFPSet.Mult1024Indexer(1L << 30, 1);
	private OffHeapDiskFPSet.Indexer bitshift = new OffHeapDiskFPSet.BitshiftingIndexer(1L << 30, 1);

	@Setup
	public void up() throws IOException {
	}

	@Setup(Level.Iteration)
	public void reseedIter() {
		// For each iteration of a benchmark, we set the seed to a known value, so that
		// each benchmark fork starts a particular iteration with the same seed.
		seed += 1;
		rng.setSeed(seed);
	}

	@Setup(Level.Trial)
	public void reseed() {
		// We reset the random number generator to a fixed seed before benchmarking a
		// specific worker count. This should help to make these benchmarks more
		// deterministic for a fixed set of benchmark parameters. The initial seed of
		// this random number generator should effectively determine what traces are
		// explored in what order by the simulation workers, so a particular seed should
		// correspond to a fixed exploration order of the behavior space.
		rng.setSeed(0);
		seed = 0;
	}

	@Benchmark
	public long InfMult() {
		return infMult.getIdx(rng.nextLong() & Long.MAX_VALUE);
	}

	@Benchmark
	public long Infinite() {
		return infinite.getIdx(rng.nextLong() & Long.MAX_VALUE);
	}

	@Benchmark
	public long Bitshift() {
		return bitshift.getIdx(rng.nextLong() & Long.MAX_VALUE);
	}

	public static void main(String[] args) throws RunnerException {
		Options opt = new OptionsBuilder().include(OffHeapIndexerBenchmark.class.getSimpleName()).build();
		new Runner(opt).run();
	}
}