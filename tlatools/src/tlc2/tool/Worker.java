// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 14:01:40 PST by lamport  
//      modified on Wed Dec  5 15:35:42 PST 2001 by yuanyu   

package tlc2.tool;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;

import tla2sany.semantic.SemanticNode;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.queue.IStateQueue;
import tlc2.util.BufferedRandomAccessFile;
import tlc2.util.IdThread;
import tlc2.util.ObjLongTable;
import tlc2.util.statistics.FixedSizedBucketStatistics;
import tlc2.util.statistics.IBucketStatistics;
import util.FileUtil;

public final class Worker extends IdThread implements IWorker {
	
	/**
	 * Multi-threading helps only when running on multiprocessors. TLC can
	 * pretty much eat up all the cycles of a processor running single threaded.
	 * We expect to get linear speedup with respect to the number of processors.
	 */
	private final ModelChecker tlc;
	private final IStateQueue squeue;
	private final ObjLongTable<SemanticNode> astCounts;
	private final IBucketStatistics outDegree;
	private final String filename;
	private final BufferedRandomAccessFile raf;

	private long lastPtr;
	private long statesGenerated;
	private int unseenSuccessorStates = 0;
	private volatile int maxLevel = 0;

	// SZ Feb 20, 2009: changed due to super type introduction
	public Worker(int id, AbstractChecker tlc, String metadir, String specFile) throws IOException {
		super(id);
		// SZ 12.04.2009: added thread name
		this.setName("TLC Worker " + id);
		this.tlc = (ModelChecker) tlc;
		this.squeue = this.tlc.theStateQueue;
		this.astCounts = new ObjLongTable<SemanticNode>(10);
		this.outDegree = new FixedSizedBucketStatistics(this.getName(), 32); // maximum outdegree of 32 appears sufficient for now.
		this.setName("TLCWorkerThread-" + String.format("%03d", id));

		this.filename = metadir + FileUtil.separator + specFile + "-" + myGetId();
		this.raf = new BufferedRandomAccessFile(filename + TLCTrace.EXT, "rw");
	}

  public final ObjLongTable<SemanticNode> getCounts() { return this.astCounts; }

	/**
   * This method gets a state from the queue, generates all the
   * possible next states of the state, checks the invariants, and
   * updates the state set and state queue.
	 */
	public void run() {
		TLCState curState = null;
		try {
			while (true) {
				curState = (TLCState) this.squeue.sDequeue();
				if (curState == null) {
					synchronized (this.tlc) {
						this.tlc.setDone();
						this.tlc.notify();
					}
					this.squeue.finishAll();
					return;
				}
				setCurrentState(curState);
				if (this.tlc.doNext(curState, this.astCounts, this)) {
					return;
				}
				
				this.outDegree.addSample(unseenSuccessorStates);
				unseenSuccessorStates = 0;
			}
		} catch (Throwable e) {
			// Something bad happened. Quit ...
			// Assert.printStack(e);
			resetCurrentState();
			synchronized (this.tlc) {
				if (this.tlc.setErrState(curState, null, true)) {
					MP.printError(EC.GENERAL, e); // LL changed call 7 April
													// 2012
				}
				this.squeue.finishAll();
				this.tlc.notify();
			}
			return;
		}
	}
	
	/* Statistics */

	final void incrementStatesGenerated(long l) {
		this.statesGenerated += l;		
	}
	
	final long getStatesGenerated() {
		return this.statesGenerated;
	}

	public final IBucketStatistics getOutDegree() {
		return this.outDegree;
	}
	
	public final int getMaxLevel() {
		return maxLevel;
	}

	final void setLevel(int level) {
		maxLevel = level;
	}

	/* Maintain trace file (to reconstruct error-trace) */
	
	/*
	 * Synchronize reads and writes to read a consistent union of all trace file
	 * fragments when one worker W wants to create the counter-example. Otherwise, we
	 * might not be able to correctly trace the path from state to an initial state.
	 * The W thread holds ModelChecker.this. The other workers might either: a) Wait
	 * on IStateQueue#sDequeue (waiting for a new state to be read from disk or
	 * added to the queue) b) Wait on ModelChecker.this (because they also found
	 * another counter-example but are blocked until we are done printing it) c)
	 * Wait on ModelChecker.this in Worker#run because the state queue is empty and
	 * they which to terminate. d) Run state space exploration The on-disk file of
	 * each worker's trace fragment is potentially inconsistent because the worker's
	 * cache in BufferedRandomAccessFile hasn't been flushed out.
	 */
	
	public final synchronized void writeState(final TLCState initialState, final long fp) throws IOException {
		// Write initial state to trace file.
		this.lastPtr = this.raf.getFilePointer();
		this.raf.writeLongNat(1L);
		this.raf.writeShortNat(myGetId());
		this.raf.writeLong(fp);
		
		// Add predecessor pointer to success state.
		initialState.workerId = (short) myGetId();
		initialState.uid = this.lastPtr;
	}

	public final synchronized void writeState(final TLCState curState, final long sucStateFp, final TLCState sucState) throws IOException {
		// Keep track of maximum diameter.
		maxLevel = Math.max(curState.getLevel() + 1, maxLevel);
		
		// Write to trace file.
		this.lastPtr = this.raf.getFilePointer();
		this.raf.writeLongNat(curState.uid);
		this.raf.writeShortNat(curState.workerId);
		this.raf.writeLong(sucStateFp);
		
		// Add predecessor pointer to success state.
		sucState.workerId = (short) myGetId();
		sucState.uid = this.lastPtr;
		
		sucState.setPredecessor(curState);
		
    	unseenSuccessorStates++;
		
//		System.err.println(String.format("<<%s, %s>>: pred=<<%s, %s>>, %s -> %s", myGetId(), this.lastPtr, 
//				curState.uid, curState.workerId,
//				curState.fingerPrint(), sucStateFp));
	}

	// Read from previously written (see writeState) trace file.
	public final synchronized ConcurrentTLCTrace.Record readStateRecord(final long ptr) throws IOException {
		this.raf.seek(ptr);
		
		final long prev = this.raf.readLongNat();
		assert 0 <= ptr;
		
		final int worker = this.raf.readShortNat();
		assert 0 <= worker && worker < tlc.workers.length;
			
		final long fp = this.raf.readLong();
		assert tlc.theFPSet.contains(fp);
		
		return new ConcurrentTLCTrace.Record(prev, worker, fp);
	}
	
	/* Checkpointing */

	public final synchronized void beginChkpt() throws IOException {
		this.raf.flush();
		final DataOutputStream dos = FileUtil.newDFOS(filename + ".tmp");
		dos.writeLong(this.raf.getFilePointer());
		dos.writeLong(this.lastPtr);
		dos.close();
	}

	public final synchronized void commitChkpt() throws IOException {
		final File oldChkpt = new File(filename + ".chkpt");
		final File newChkpt = new File(filename + ".tmp");
		if ((oldChkpt.exists() && !oldChkpt.delete()) || !newChkpt.renameTo(oldChkpt)) {
			throw new IOException("Trace.commitChkpt: cannot delete " + oldChkpt);
		}
	}

	public final void recover() throws IOException {
		final DataInputStream dis = FileUtil.newDFIS(filename + ".chkpt");
		final long filePos = dis.readLong();
		this.lastPtr = dis.readLong();
		dis.close();
		this.raf.seek(filePos);
	}
	
	/* Enumerator */
	
	public final Enumerator elements() throws IOException {
		return new Enumerator();
	}

	public class Enumerator {

		private final long len;
		private final BufferedRandomAccessFile enumRaf;

		Enumerator() throws IOException {
			this.len = raf.getFilePointer();
			this.enumRaf = new BufferedRandomAccessFile(filename + TLCTrace.EXT, "r");
		}

		public boolean hasMoreFP() {
			final long fpos = this.enumRaf.getFilePointer();
			if (fpos < this.len) {
				return true;
			}
			return false;
		}

		public long nextFP() throws IOException {
			this.enumRaf.readLongNat(); /* drop */
			this.enumRaf.readShortNat(); /* drop */
			return this.enumRaf.readLong();
		}

		public void close() throws IOException {
			this.enumRaf.close();
		}
	}
}
