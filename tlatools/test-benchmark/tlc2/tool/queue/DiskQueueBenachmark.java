/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved.
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
package tlc2.tool.queue;

import java.io.IOException;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.BenchmarkMode;
import org.openjdk.jmh.annotations.Group;
import org.openjdk.jmh.annotations.GroupThreads;
import org.openjdk.jmh.annotations.Mode;
import org.openjdk.jmh.annotations.Param;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.State;
import org.openjdk.jmh.annotations.TearDown;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import tlc2.tool.TLCState;
import tlc2.tool.TLCStates;
import tlc2.util.FlightRecorderProfiler;

@State(Scope.Group)
@BenchmarkMode(Mode.Throughput)
public class DiskQueueBenachmark {
	
	@Param({"1", "2", "4", "8", "16", "32", "64"})
	public int vars;

	@Param({"DiskByteArrayQueue", "DiskStateQueue"})
	public String impl;
	
	private IStateQueue dsq;

	private TLCState state;
	
    @Setup
    public void up() throws IOException {
		if (impl.equals("DiskByteArrayQueue")) {
			this.dsq = new DiskByteArrayQueue();
		} else {
			this.dsq = new DiskStateQueue();
		}

		this.state = TLCStates.createDummyState(vars);
    }
    
    @TearDown
    public void down() throws IOException {
    	this.dsq.delete();
    }
    
    @Benchmark
    @Group("g02")
    @GroupThreads(1)
    public TLCState consumer1() {
        return this.dsq.sDequeue();
    }

    @Benchmark
    @Group("g02")
    @GroupThreads(1)
    public void producer1() {
    	this.dsq.sEnqueue(this.state);
    }
    
    
    @Benchmark
    @Group("g04")
    @GroupThreads(2)
    public TLCState consumer2() {
        return this.dsq.sDequeue();
    }

    @Benchmark
    @Group("g04")
    @GroupThreads(2)
    public void producer2() {
    	this.dsq.sEnqueue(this.state);
    }

    
    @Benchmark
    @Group("g08")
    @GroupThreads(4)
    public TLCState consumer4() {
        return this.dsq.sDequeue();
    }

    @Benchmark
    @Group("g08")
    @GroupThreads(4)
    public void producer4() {
    	this.dsq.sEnqueue(this.state);
    }

    
    @Benchmark
    @Group("g16")
    @GroupThreads(8)
    public TLCState consumer8() {
        return this.dsq.sDequeue();
    }

    @Benchmark
    @Group("g16")
    @GroupThreads(8)
    public void producer8() {
    	this.dsq.sEnqueue(this.state);
    }
    
    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(DiskQueueBenachmark.class.getSimpleName())
                .addProfiler(FlightRecorderProfiler.class)
                .build();

        new Runner(opt).run();
    }
}
