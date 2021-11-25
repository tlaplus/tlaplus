/*******************************************************************************
 * Copyright (c) 2021 Microsoft Research. All rights reserved.
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

import java.util.Arrays;
import java.util.Collections;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.Level;
import org.openjdk.jmh.annotations.Param;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.State;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import tlc2.util.FP64;
import tlc2.value.RandomEnumerableValues;

@State(Scope.Benchmark)
public class FcnRcdBenchmark {

	static {
		RandomEnumerableValues.setSeed(15041980L);
		RandomEnumerableValues.reset();

		FP64.Init();
	}
	
	@Param({"0", "2", "4", "8", "16", "32", "64", "128", "256", "512", "1024", "2048", "4096", "8192"})
	public int size;

	public FcnRcdValue fcnRcd;
		
	@Setup(Level.Iteration)
	public void setup() {
		Value[] domain = new Value[size];
		Value[] range = new Value[size];
		for (int i = 0; i < domain.length; i++) {
			// Use values as domain for which equality checking isn't effectively for free. 
			domain[i] = new StringValue("asdfghjkoiuytrewqzxcvbn" + i);
//			domain[i] = IntValue.gen(i);
			range[i] = IntValue.gen(i);
		}
		Collections.shuffle(Arrays.asList(domain));
		fcnRcd = (FcnRcdValue) new FcnRcdValue(domain, range, false).normalize();
	}

//	@Benchmark
//	public Value[] fcnRcdValueSelectIndex() {
//		Value[] values = new Value[size];
//		for (int i = 0; i < values.length; i++) {
//			Value domain = new StringValue("asdfghjkoiuytrewqzxcvbn" + i);
//			values[i] = fcnRcd.selectIndexTable(domain);
////			values[i] = fcnRcd.select(IntValue.gen(i));
//		}
//		return values;
//	}

	@Benchmark
	public Value[] fcnRcdValueSelectNoIndex() {
		Value[] values = new Value[size];
		for (int i = 0; i < values.length; i++) {
			Value domain = new StringValue("asdfghjkoiuytrewqzxcvbn" + i);
			values[i] = fcnRcd.selectLinearSearch(domain);
//			values[i] = fcnRcd.selectNoIndex(IntValue.gen(i));
		}
		return values;
	}
	
	@Benchmark
	public Value[] fcnRcdValueSelectBinarySearch() {
		Value[] values = new Value[size];
		for (int i = 0; i < values.length; i++) {
			Value domain = new StringValue("asdfghjkoiuytrewqzxcvbn" + i);
			values[i] = fcnRcd.selectBinarySearch(domain);
//			values[i] = fcnRcd.selectNoIndex(IntValue.gen(i));
		}
		return values;
	}
	
    public static void main(String[] args) throws RunnerException {
        final Options opt = new OptionsBuilder()
                .include(FcnRcdBenchmark.class.getSimpleName())
                .build();
        new Runner(opt).run();
    }
}
