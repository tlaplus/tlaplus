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
package tlc2.tool;

import java.io.IOException;

import tlc2.TLCGlobals;
import tlc2.util.LongVec;

/**
 * This implementation of a Trace is concurrent in that multiple workers can add
 * states to it whereas with {@link TLCTrace} concurrent adds/appends block and
 * are serialized. The latter has been identified to be a scalability bottleneck
 * of bread-first search (safety checking).
 * <p>
 * {@link ConcurrentTLCTrace} - in comparison to {@link TLCTrace} - maintains
 * one trace file per worker and thus supports concurrent appends: Each worker
 * adds/appends an entry to its (dedicate) file. When a counter-example has to be
 * created, the actual error-trace gets created from the union of all (partial)
 * trace files.
 */
public class ConcurrentTLCTrace extends TLCTrace {
	
	private final Worker workers[];

	public ConcurrentTLCTrace(String metadir, String specFile, TraceApp tool) throws IOException {
		super(metadir, specFile, tool);
		this.workers = new Worker[TLCGlobals.getNumWorkers()];
	}

	public Worker addWorker(Worker worker) {
		this.workers[worker.myGetId()] = worker;
		return worker;
	}

	/**
	 * @see ConcurrentTLCTrace#getLevel()
	 */
	@Override
	public final int getLevelForReporting() throws IOException {
		return getLevel();
	}

	@Override
	public synchronized final int getLevel() throws IOException {
		int maxLevel = 1; // With a single, init state the level/progress/diameter is 1, not 0!
		for (Worker worker : workers) {
			maxLevel = Math.max(maxLevel, worker.getMaxLevel());
		}
		return maxLevel;
	}

	private TLCStateInfo[] getTrace(final TLCState state) throws IOException {
		final LongVec fps = new LongVec();

		// Starting at the given start fingerprint (which is the end of the
		// trace from the point of the initial states), the sequence of
		// predecessors fingerprints are reconstructed from the trace files up to
		// an initial state.
		synchronized (this) {
			Record record = Record.getPredecessor(state, this.workers);
			while (!record.isInitial()) {
				fps.addElement(record.fp);
				record = record.getPredecessor();
			}
			// The fp of the final initial state.
			fps.addElement(record.fp);
			assert 0 <= fps.size() && fps.size() <= getLevel();
		}
		
		return getTrace(fps);
	}

	/**
	 * Write out a sequence of states that reaches s2 from an initial state,
	 * according to the spec. s2 is a next state of s1.
	 * 
	 * @param s1
	 *            may not be null.
	 * @param s2
	 *            may be null.
	 * @throws IOException
	 * @throws WorkerException
	 */
	public void printTrace(final TLCState s1, final TLCState s2) throws IOException, WorkerException {
		if (s1.isInitial()) {
			printTrace(s1, s2, new TLCStateInfo[0]);
		} else {
			printTrace(s1, s2, getTrace(s1));
		}
	}

	/* Checkpoint. */
	
	public synchronized void beginChkpt() throws IOException {
		for (Worker worker : workers) {
			worker.beginChkpt();
		}
	}

	public void commitChkpt() throws IOException {
		for (Worker worker : workers) {
			worker.commitChkpt();
		}
	}

	public void recover() throws IOException { 
		// TODO Check that the number of disk .st files is >= workers.length. If it is
		// lower, TLC runs with fewer workers than when the checkpoint was taken. Take
		// this case into account.
		
		for (Worker worker : workers) {
			worker.recover();
		}
	}
	
	/* Enumerator */
	
	public synchronized Enumerator elements() throws IOException {
		final Worker.Enumerator[] enums = new Worker.Enumerator[workers.length];
		for (int j = 0; j < workers.length; j++) {
			enums[j] = workers[j].elements();
		}
		return new Enumerator() {
			private int idx = 0;
			
			@Override
			public long nextPos() {
				if (idx >= workers.length) {
					return -1L;
				}
				if (enums[idx].hasMoreFP()) {
					return 42L;
				} else if (idx + 1 >= workers.length) {
					return -1L;
				} else {
					idx = idx + 1;
					return enums[idx].hasMoreFP() ? 42L : -1L;	
				}
			}

			@Override
			public long nextFP() throws IOException {
				if (!enums[idx].hasMoreFP()) {
					idx = idx + 1;
				}
				return enums[idx].nextFP();
			}

			@Override
			public void close() throws IOException {
				for (Worker.Enumerator enumerator : enums) {
					enumerator.close();
				}
			}

			@Override
			public void reset(long i) throws IOException {
				idx = 0;
			}
		};
	}
	
	public static class Record {
		

		static Record getPredecessor(final TLCState state, final Worker[] workers) throws IOException {
			Record record = workers[state.workerId].readStateRecord(state.uid);
			record.workers = workers;
			return record.getPredecessor();
		}

		private final long ptr;
		private final int worker;
		private final long fp;
		private Worker[] workers;

		public Record(final long ptr, final int worker, final long fp) {
			this.ptr = ptr;
			this.worker = worker;
			this.fp = fp;
		}
		
		public Worker getWorker() {
			return this.workers[this.worker];
		}

		public boolean isInitial() {
			return ptr == 1L;
		}

		@Override
		public String toString() {
			return "Record [ptr=" + ptr + ", worker=" + worker + ", fp=" + fp + ", initial=" + isInitial() + "]";
		}
		
		Record getPredecessor() throws IOException {
			final Record record = getWorker().readStateRecord(this.ptr);
			record.workers = this.workers;
			return record;
		}
	}
}
