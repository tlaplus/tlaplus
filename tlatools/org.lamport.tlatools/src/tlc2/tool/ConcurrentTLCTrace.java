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

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.util.LongVec;
import tlc2.value.RandomEnumerableValues;

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

	/**
	 * @see TLCTrace#getTrace(LongVec)
	 */
	public TLCStateInfo[] getTrace(final TLCState state) throws IOException {
		if (state.isInitial()) {
			return new TLCStateInfo[] {new TLCStateInfo(state)};
		}
		
		final List<Record> records = new ArrayList<>(state.getLevel());
		records.add(Record.getRecord(state, this.workers));

		// Starting at the given start fingerprint (which is the end of the
		// trace from the point of the initial states), the sequence of
		// predecessors fingerprints are reconstructed from the trace files up to
		// an initial state.
		synchronized (this) {
			Record record = Record.getPredecessor(state, this.workers);
			while (!record.isInitial()) {
				records.add(record);
				record = record.getPredecessor();
			}
			// The fp of the final initial state.
			records.add(record);
			assert 0 <= records.size() && records.size() <= getLevel();
			return getTrace(null, records);
		}
	}
	
	public TLCStateInfo[] getTrace(final TLCState from, final TLCState to) throws IOException {
		if (to.isInitial() || from.equals(to)) {
			return new TLCStateInfo[] {new TLCStateInfo(to)};
		}
		
		final List<Record> records = new ArrayList<>(to.getLevel() - from.getLevel());
		records.add(Record.getRecord(to, this.workers));
		
		// Starting at the given start fingerprint (which is the end of the
		// trace from the point of the initial states), the sequence of
		// predecessors fingerprints are reconstructed from the trace files up to
		// an initial state.
		synchronized (this) {
			Record record = Record.getPredecessor(to, this.workers);
			while (record.fp != from.fingerPrint()) {
				records.add(record);
				record = record.getPredecessor();
			}
			// The fp of the final initial state.
			records.add(record);
			assert 0 <= records.size() && records.size() <= getLevel();

			return getTrace(new TLCStateInfo(from), records);
		}
	}

	protected final TLCStateInfo[] getTrace(TLCStateInfo sinfo, final List<Record> records) {
		// Re-Initialize the rng with the seed value recorded and used during the model
		// checking phase. Otherwise, we won't be able to reconstruct the error trace
		// because the set of initial states is likely to be different.
		// This is only necessary though, if TLCGlobals.enumFraction was < 1 during
		// the generation of inits.
		final Random snapshot = RandomEnumerableValues.reset();
		
		// The vector of fingerprints is now being followed forward from the
		// initial state (which is the last state in the long vector), to the
		// end state.
		//
		// At each fingerprint of the sequence, the equivalent state gets
		// reconstructed. For the initial state it's just the fingerprint, for
		// successor states the predecessor p to the successor state s and the
		// fingerprint that are passed to Tool. Tool generates *all* next states
		// of p and throws away all except the one that has a matching
		// fingerprint.
		int stateNum = 0;
		final int len = records.size() - 1;
		final TLCStateInfo[] res = new TLCStateInfo[len];
		if (len > 0) {
			if (sinfo == null) {
				// Recreate initial state from its fingerprint.
				Record record = records.get(len);
				assert record.isInitial();
				sinfo = this.tool.getState(record.fp);
				
				Record prev = records.get(len - 1);
				sinfo.state.workerId = (short) prev.worker;
				sinfo.state.uid = prev.ptr;
			}
			// Recover successor states from its predecessor and its fingerprint.
			res[stateNum++] = sinfo;
			for (int i = len-2; i >= 0; i--) {
				Record record = records.get(i+1);
				long fp = record.fp;
				sinfo = this.tool.getState(fp, sinfo.state);
				if (sinfo == null) {
					/*
					 * The following error message is misleading, because it's triggered when TLC
					 * can't find a non-initial state from its fingerprint when it's generating an
					 * error trace. LL 7 Mar 2012
					 */
					MP.printError(EC.TLC_FAILED_TO_RECOVER_INIT);
					MP.printError(EC.TLC_BUG, "2 " + Long.toString(fp));
					System.exit(1);
				}
				Record prev = records.get(i);
				sinfo.state.workerId = (short) prev.worker;
				sinfo.state.uid = prev.ptr;
				
				res[stateNum++] = sinfo;
			}
		}
		RandomEnumerableValues.set(snapshot);
		return res;
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
		// MAK 06/08/2020:
		// Touch MC.st.chkpt (in addition to the worker-created MC-${N}.chkpt files)
		// that (single-worker) TLCTrace creates. The Toolbox checks for the existence
		// of checkpoints by looking for this file (see
		// org.lamport.tla.toolbox.tool.tlc.model.Model.getCheckpoints(boolean)). If 
		// the Toolbox check fails, a user cannot resume/restart model-checking from
		// the checkpoint. Addresses Github issue #469 at
		// https://github.com/tlaplus/tlaplus/issues/469
		//
		// We create an empty file here instead of changing the Toolbox in case 3rd party
		// integrations and scripts rely on the file's existence.  Reading the empty
		// MC.st.chkpt with an older TLC release will crash and thus make a user aware
		// that recovery fails.
		//
		// createNewFile is safe to call periodically when a checkpoint get taken
		// because it does *not* throw an exception if the file already exists.
		new File(filename + ".chkpt").createNewFile();
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
		
        static Record getRecord(final TLCState state, final Worker[] workers) throws IOException {
			final Record record = workers[state.workerId].readStateRecord(state.uid);
			record.workers = workers;
			return record;
        }
		
		static Record getPredecessor(final TLCState state, final Worker[] workers) throws IOException {
			return getRecord(state, workers).getPredecessor();
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
