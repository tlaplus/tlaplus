/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved.
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

import org.junit.Test;

import gov.nasa.jpf.util.test.TestJPF;
import tlc2.tool.TLCState;

public class StateQueueJPFTest extends TestJPF {

    private final StateQueue queue = new DummyStateQueue();
    private final TLCState tlcState = new DummyTLCState();
    private final Thread mainThread = new Thread(new MainTask(queue), "Main");
    private final Thread[] workerThreads = new Thread[3];

    public StateQueueJPFTest() {
        // Initialize the worker threads
        for (int i = 0; i < workerThreads.length; i++) {
            workerThreads[i] = new Thread(new WorkerTask(queue, tlcState), "Worker" + i);
        }
    }

    public static void main(String[] args) {
        new StateQueueJPFTest().test();
    }

    @Test
    public void test() {
        if (verifyNoPropertyViolation()) {
            try {
                // Start the threads only if they are not already started
                mainThread.start();

                for (Thread worker : workerThreads) {
                    if (!worker.isAlive()) {
                        worker.start();
                    }
                }

                // Ensure all threads complete before exiting the test
                mainThread.join();
                for (Thread worker : workerThreads) {
                    worker.join();
                }
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
    }

    private static class MainTask implements Runnable {
        private final StateQueue queue;

        public MainTask(StateQueue queue) {
            this.queue = queue;
        }

        @Override
        public void run() {
            queue.suspendAll();
            // critical section (taking a checkpoint)
            queue.resumeAll();
        }
    }

    private static class WorkerTask implements Runnable {
        private final StateQueue queue;
        private final TLCState tlcState;

        public WorkerTask(StateQueue queue, TLCState tlcState) {
            this.queue = queue;
            this.tlcState = tlcState;
        }

        @Override
        public void run() {
            for (int i = 0; i < 3; i++) {
                TLCState state = queue.dequeue();
                if (state == null) {
                    queue.finishAll();
                    return;
                }
                queue.enqueue(tlcState);
            }
            queue.finishAll();
        }
    }

    private static class DummyStateQueue extends StateQueue {

        private TLCState state;

        void enqueueInner(TLCState state) {
            this.state = state;
        }

        TLCState dequeueInner() {
            return state;
        }

        TLCState peekInner() {
            return state;
        }

        public void beginChkpt() throws IOException {
            // checkpointing not being verified
        }

        public void commitChkpt() throws IOException {
            // checkpointing not being verified
        }

        public void recover() throws IOException {
            // checkpointing not being verified
        }
    }
}
