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
package tlc2.tool.queue;

import java.io.IOException;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.Group;
import org.openjdk.jmh.annotations.GroupThreads;
import org.openjdk.jmh.annotations.Param;
import org.openjdk.jmh.annotations.Scope;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.State;
import org.openjdk.jmh.annotations.TearDown;

import tlc2.tool.TLCState;
import tlc2.tool.TLCStates;

@State(Scope.Group)
public class StateQueueBenachmark {

	@Param({"1", "2", "4", "8", "16", "32", "64"})
	public int size;
	
	private IStateQueue s;

	private TLCState[] batch;

    @Setup
    public void up() throws IOException {
        s = new DiskStateQueue();
        
    	// balance off the costs for creating the TLCState[].
    	this.batch = new TLCState[size];
    	for (int i = 0; i < batch.length; i++) {
			batch[i] = TLCStates.createDummyState();
		}
    }
    
    @TearDown
    public void down() throws IOException {
    	this.s.delete();
    }
  
    @Benchmark
    @Group("single")
    @GroupThreads(2)
    public TLCState[] consumerSingle() {
    	final TLCState[] res = new TLCState[batch.length];
    	for (int i = 0; i < batch.length; i++) {
    		res[i] = this.s.sDequeue();
    	}
        return res;
    }

    @Benchmark
    @Group("single")
    @GroupThreads(2)
    public void producerSingle() {
    	for (int i = 0; i < batch.length; i++) {
    		this.s.sEnqueue(batch[i]);
		}
    }

    
    /* Batches of enqueue only */
    
    @Benchmark
    @Group("batchasym")
    @GroupThreads(2)
    public TLCState[] consumerBatch() {
    	final TLCState[] res = new TLCState[batch.length];
    	for (int i = 0; i < batch.length; i++) {
    		res[i] = this.s.sDequeue();
    	}
        return res;
    }

    @Benchmark
    @Group("batchasym")
    @GroupThreads(2)
    public void producerBatch() {
    	this.s.sEnqueue(batch);
    }

    
    /* Batches of dequeue & enqueue */
    
    @Benchmark
    @Group("batchsym")
    @GroupThreads(2)
    public TLCState[] consumerBatchSym() {
        return this.s.sDequeue(size);
    }

    @Benchmark
    @Group("batchsym")
    @GroupThreads(2)
    public void producerBatchSym() {
    	this.s.sEnqueue(batch);
    }
}
