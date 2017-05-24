// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:30:03 PST by lamport
//      modified on Wed Nov 14 23:26:07 PST 2001 by yuanyu
//      modified on Wed Jun 28 12:00:16 PDT 2000 by rjoshi

package tlc2.tool;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.output.StatePrinter;
import tlc2.util.BufferedRandomAccessFile;
import tlc2.util.LongVec;
import util.FileUtil;

public class TLCTrace {

	private static String filename;
	private BufferedRandomAccessFile raf;
	private long lastPtr;
	// TODO This arrays causes coherence. This problem is easily removed by
	// storing each ptr in lastPtrs in the corresponding worker. That's a little
	// bit ugly though in terms of separation of concerns. The current solution
	// confines all related aspects to TLCTrace. 
	private final long[] lastPtrs = new long[TLCGlobals.getNumWorkers()];
	private TraceApp tool;

  public TLCTrace(String metadir, String specFile, TraceApp tool)
  throws IOException {
		filename = metadir + FileUtil.separator + specFile + ".st";
		this.raf = new BufferedRandomAccessFile(filename, "rw");
		this.lastPtr = 1L;
		this.tool = tool;
	}

	/**
   * @param fp A finger print of a state without a predecessor (init state)
	 * @return The new location (pointer) for the given finger print (state)
	 * @throws IOException
	 */
  public final synchronized long writeState(final long aFingerprint)
  throws IOException {
		return writeState(1, aFingerprint);
	}

	/**
   * @param predecessor The predecessor state
   * @param fp A finger print
	 * @return The new location (pointer) for the given finger print (state)
	 * @throws IOException
	 */
  public final synchronized long writeState(final TLCState predecessor, final long aFingerprint)
  throws IOException {
		return writeState(predecessor.uid, aFingerprint);
	}

  public final synchronized long writeState(final TLCState predecessor, final long aFingerprint, final IWorker worker)
  throws IOException {
		final long lastPtr = writeState(predecessor.uid, aFingerprint);
		this.lastPtrs[worker.myGetId()] = lastPtr;
		return lastPtr;
	}
  
	/**
   * @param predecessorLoc The location of the state predecessor
   * @param fp A finger print
	 * @return The new location (pointer) for the given finger print (state)
	 * @throws IOException
	 */
  private final synchronized long writeState(long predecessorLoc, long fp)
  throws IOException {
		// TODO Remove synchronization as all threads content for this lock
		this.lastPtr = this.raf.getFilePointer();
		this.raf.writeLongNat(predecessorLoc);
		this.raf.writeLong(fp);
		return this.lastPtr;
	}

	public final void close() throws IOException {
		this.raf.close();
	}

	private synchronized long getPrev(long loc) throws IOException {
		this.raf.seek(loc);
		return this.raf.readLongNat();
	}

	private synchronized long getFP(long loc) throws IOException {
		this.raf.seek(loc);
		this.raf.readLongNat(); /* drop */
		return this.raf.readLong();
	}

	/**
	 * The level is the length of the longest path in the execution trees
	 * (forest) (his forest is stored in the trace file).
	 * <p>
	 * With multiple workers, the level is an approximation. With multiple
	 * workers, the forest has an unknown number of leafs and we do not know the
	 * position of leafs in the trace file.
	 * <p>
	 * We know however the vertices, that the set of workers last added to the
	 * forest. Thus, we calculate the lengths of each path or path fragment
	 * from those vertices. The maximum length is then our approximation of the
	 * longest path. It's not elegant but good enough for now.
	 * 
	 * @see TLCTrace#getLevel()
	 */
	public final synchronized int getLevelForFinalReporting() throws IOException {
		// TODO We generally assume the length and the number of workers to be
		// relatively small to not warrant parallelization. The current
		// getLevel(lastPtr) cannot be called concurrently, because it uses a
		// single BufferedRandomAccessFile.
		int max = 0;
		for (long lastPtr : lastPtrs) {
			max = Math.max(max, lastPtr > 0 ? getLevel(lastPtr) : 0);
		}
		return max;
	}

	/**
	 * Returns the level (monotonically increasing)!
	 * 
	 * LL: The user has no real need of an accurate tree height. Breadth-first
	 * search is good because it provides the shortest possible error trace.
	 * Usually approximately breadth-first search is just as good because it
	 * makes little difference if the error trace isn't quite as short as
	 * possible. I believe that in most applications, after a short initial
	 * period, the height of the tree grows slowly. All workers are usually
	 * working on states of the same height except for brief periods when the
	 * height changes, and then the heights will differ by at most one.
	 * Reporting the height to the user gives him some information about how
	 * fast model checking is going. He will have no problem getting used to the
	 * idea that it's only an approximation. (I expect that few users even know
	 * what it means.) I'd like to make the reported value be monotonic because,
	 * if it's not, users may worry and people already have enough things in
	 * life to worry about.
	 * 
	 * @see TLCTrace#getLevel()
	 */
	public final synchronized int getLevelForReporting() throws IOException {
		final int calculatedLevel = getLevel(this.lastPtr);
		if (calculatedLevel > previousLevel) {
			previousLevel = calculatedLevel;
		}
		return previousLevel;
	}

	/**
	 * Stores the previous level reported to guarantee that it is monotonic
	 */
	private int previousLevel;

	/**
	 * @see TLCTrace#getLevel(long)
	 * @return 1 to the length of the longest behavior found so far.
	 */
	public final int getLevel() throws IOException {
	    // This assumption (lastPtr) only holds for the TLC in non-parallel mode.
		// Generally the last line (logically a state) is not necessarily
		// on the highest level of the state tree, which is only true if
		// states are explored with strict breadth-first search.
		//
		// The (execution) trace is a forest of one to n trees, where each path 
		// in the forest represents the order in which states have been generated
		// by the workers.
		// The algorithm, with which the diameter is approximated from the trace,
		// is pretty simple; too simple. The trace is constantly written to the .st
		// file where each "record" in the file is a link from a successor state to
		// its predecessor state. Thus, the link is a position in the trace file
		// where the predecessor state - actually its fingerprint - is stored. At
		// the end of the trace file, there are up to m leaf records for which no
		// successors have been appended (yet, assuming there are any).
		//
		// Once the workers have terminated, TLC traverses the trace from a leaf record
		// back to a root record. This height is what is reported as the diameter. 
		// The selection, from what leaf record TLC starts the traversal, is based on
		// the last record inserted into the trace file. If this record is one with a
		// low height (because its corresponding worker waited most of the time), the
		// diameter will thus be underreport. If, on the other hand, the last record 
		// happens to be one with a large height, the diameter will be overreported.
		// 
		// The selection of the leaf record is the source of the algorithm's 
		// non-determinism. With a single worker, the last record in the trace is
		// always the same which always corresponds to the longest behavior found so 
		// far (strict BFS). This invariant does not hold with multiple workers.
        //
		// Obviously, with multiple workers the approximation of the diameter will
		// improve with the size of the state graph. Assuming a well-shaped state graph,
		// we can argue that the approximation is good enough and document, that its 
		// value can be anything from 1 to the longest behavior found so far.
		return getLevel(this.lastPtr);
	}

	/**
	 * @param startLoc
	 *            The start location (pointer) from where the level (height) of
	 *            the path in the execution tree should be calculated.
	 * @return The level (height) of the path in the execution tree (the trace)
	 *         starting at startLoc.
	 * @throws IOException
	 */
	public synchronized final int getLevel(long startLoc) throws IOException {
		// keep current location
		long currentFilePointer = this.raf.getFilePointer();

		// calculate level/depth based on start location
		int level = 0;
	for (long predecessorLoc = startLoc; predecessorLoc != 1; predecessorLoc = this
				.getPrev(predecessorLoc)) {
			level++;
		}

		// rewind to current location
		this.raf.seek(currentFilePointer);
		return level;
	}

	/**
	 * @return All states in the trace file
	 * @throws IOException
	 */
	public final TLCStateInfo[] getTrace() throws IOException {
		final Map<Long, TLCStateInfo> locToState = new HashMap<Long, TLCStateInfo>();

		synchronized (this) {
			final long curLoc = this.raf.getFilePointer();
			try {
				long length = this.raf.length();
				// go to first byte
				this.raf.seek(0);

				// read init state
				this.raf.readLongNat(); /* drop predecessor of init state */
				TLCStateInfo state = this.tool.getState(this.raf.readLong());
				locToState.put(0L, state);

				for (long location = 12; location < length; location += 12) {
					final long predecessorLocation = this.raf.readLongNat();
					final long fp = this.raf.readLong();

					// read predecessor from map
					final TLCStateInfo predecessor = locToState.get(predecessorLocation);

					// reconstruct current state
					state = this.tool.getState(fp, predecessor.state);

					// chain to predecessor
					state.predecessorState = predecessor;
					state.stateNumber = location / 12;

					// store in map
					locToState.put(location, state);
				}

			} finally {
				// rewind
				this.raf.seek(curLoc);
			}
		}

		return locToState.values().toArray(new TLCStateInfo[locToState.size()]);
	}

	/**
   * @param loc The start location (pointer) from where the trace should be computed
   * @param included true if the start location state should be included
	 * @return An array of predecessor states
	 * @throws IOException
	 */
  public final TLCStateInfo[] getTrace(long loc, boolean included)
  throws IOException {
    LongVec fps = new LongVec();

		// Starting at the given start fingerprint (which is the end of the
		// trace from the point of the initial states), the chain of
		// predecessors fingerprints are reconstructed from the trace file up to
		// the initial state.
		synchronized (this) {
			long curLoc = this.raf.getFilePointer();
			long loc1 = (included) ? loc : this.getPrev(loc);
			for (long ploc = loc1; ploc != 1; ploc = this.getPrev(ploc)) {
				fps.addElement(this.getFP(ploc));
			}
			this.raf.seek(curLoc);
		}

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
		final int len = fps.size();
		final TLCStateInfo[] res = new TLCStateInfo[len];
		if (len > 0) {
			// Recover initial state from its fingerprint.
			long fp = fps.elementAt(len - 1);
			TLCStateInfo sinfo = this.tool.getState(fp);
      if (sinfo == null) 
      {
				MP.printError(EC.TLC_FAILED_TO_RECOVER_INIT);
				MP.printError(EC.TLC_BUG, "1");
				System.exit(1);
			}
			// Recover successor states from its predecessor and its fingerprint.
			res[stateNum++] = sinfo;
			for (int i = len - 2; i >= 0; i--) {
				fp = fps.elementAt(i);
				sinfo = this.tool.getState(fp, sinfo.state);
				if (sinfo == null) {
					/*
	     * The following error message is misleading, because it's triggered
	     * when TLC can't find a non-initial state from its fingerprint
	     * when it's generating an error trace.  LL 7 Mar 2012
					 */
					MP.printError(EC.TLC_FAILED_TO_RECOVER_INIT);
					MP.printError(EC.TLC_BUG, "2");
					System.exit(1);
				}
				res[stateNum++] = sinfo;
			}
		}
		return res;
	}

	/**
   * Write out a sequence of states that reaches s2 from an initial
   * state, according to the spec. s2 is a next state of s1.
	 * 
   * @param s1 may not be null.
   * @param s2 may be null.
	 * @throws IOException
	 * @throws WorkerException
	 */
	public synchronized final void printTrace(final TLCState s1, final TLCState s2)
  throws IOException, WorkerException 
  {
		MP.printError(EC.TLC_BEHAVIOR_UP_TO_THIS_POINT);
		// Print the prefix leading to s1:
		long loc1 = s1.uid;
		TLCState lastState = null;
		TLCStateInfo[] prefix = this.getTrace(loc1, false);
		int idx = 0;
      while (idx < prefix.length) 
      {
			StatePrinter.printState(prefix[idx], lastState, idx + 1);
			lastState = prefix[idx].state;
			idx++;
		}

		// Print s1:
		TLCStateInfo sinfo;
		// If the prefix is of length zero, s1 is an initial state. If the
		// prefix has elements, use the last state in prefix as the predecessor
		// to s1.
		if (prefix.length == 0) {
			sinfo = this.tool.getState(s1.fingerPrint());
          if (sinfo == null) 
          {
				MP.printError(EC.TLC_FAILED_TO_RECOVER_INIT);
				MP.printError(EC.TLC_BUG, "3");
				System.exit(1);
			}
      }
      else 
      {
			TLCState s0 = prefix[prefix.length - 1].state;
			sinfo = this.tool.getState(s1.fingerPrint(), s0);
          if (sinfo == null) 
          {
				MP.printError(EC.TLC_FAILED_TO_RECOVER_INIT);
				MP.printError(EC.TLC_BUG, "4");
				StatePrinter.printState(s1);
				System.exit(1);
			}
		}
      if (s2 == null) 
      { 
			lastState = null;
		}
		StatePrinter.printState(sinfo, lastState, ++idx);
		lastState = sinfo.state;

		// Print s2:
		// The predecessor to s2 is s1.
		if (s2 != null) {
			sinfo = this.tool.getState(s2, s1);
          if (sinfo == null) 
          {
				MP.printError(EC.TLC_FAILED_TO_RECOVER_INIT);
				MP.printError(EC.TLC_BUG, "5");
				StatePrinter.printState(s2);
				System.exit(1);
			}
			StatePrinter.printState(sinfo, null, ++idx);
		}
	}

	/**
   * Returns a sequence of states that reaches, but excludes the
   * state with fingerprint fp.
	 */
	@SuppressWarnings("unused")
	private final TLCStateInfo[] printPrefix(long fp) throws IOException {
		// First, find the location for fp:
		this.raf.seek(0);
		this.raf.readLongNat(); /* drop */

		while (this.raf.readLong() != fp) {
			this.raf.readLongNat(); /* drop */
		}

		// Print the states corresponding to the fps:
		TLCState lastState = null;
		TLCStateInfo[] prefix = this.getTrace(this.lastPtr, false);
		int idx = 0;
		while (idx < prefix.length) {
			StatePrinter.printState(prefix[idx], lastState, idx + 1);
			lastState = prefix[idx].state;
			idx++;
		}
		return prefix;
	}

	/* Checkpoint. */
	public synchronized final void beginChkpt() throws IOException {
		this.raf.flush();
		// SZ Feb 24, 2009: FileUtil introduced
		DataOutputStream dos = FileUtil.newDFOS(filename + ".tmp");
		dos.writeLong(this.raf.getFilePointer());
		dos.writeLong(this.lastPtr);
		dos.close();
	}

	public final void commitChkpt() throws IOException {
		File oldChkpt = new File(filename + ".chkpt");
		File newChkpt = new File(filename + ".tmp");
    if ((oldChkpt.exists() && !oldChkpt.delete()) ||
	!newChkpt.renameTo(oldChkpt)) {
			throw new IOException("Trace.commitChkpt: cannot delete " + oldChkpt);
		}
	}

	public final void recover() throws IOException {
		// SZ Feb 24, 2009: FileUtil introduced
		DataInputStream dis = FileUtil.newDFIS(filename + ".chkpt");
		long filePos = dis.readLong();
		this.lastPtr = dis.readLong();
		dis.close();
		this.raf.seek(filePos);
	}

  public static String getFilename() { return filename; }

	public static long getRecoverPtr() throws IOException {
		// SZ Feb 24, 2009: FileUtil introduced
		DataInputStream dis = FileUtil.newDFIS(filename + ".chkpt");
		long res = dis.readLong();
		dis.close();
		return res;
	}

	@SuppressWarnings("unused")
	private long[] addBlock(long fp[], long prev[]) throws IOException {
		// Reuse prev.
		for (int i = 0; i < fp.length; i++) {
			prev[i] = this.writeState(prev[i], fp[i]);
		}
		return prev;
	}

	public synchronized final Enumerator elements() throws IOException {
		return new Enumerator();
	}

	final class Enumerator {
		long len;
		BufferedRandomAccessFile enumRaf;

		Enumerator() throws IOException {
			this.len = raf.length();
			this.enumRaf = new BufferedRandomAccessFile(filename, "r");
		}

		final void reset(long pos) throws IOException {
			this.len = raf.length();
			if (pos == -1) {
				pos = this.enumRaf.getFilePointer();
			}
			this.enumRaf = new BufferedRandomAccessFile(filename, "r");
			this.enumRaf.seek(pos);
		}

		final long nextPos() {
			long fpos = this.enumRaf.getFilePointer();
      if (fpos < this.len) { return fpos; }
			return -1;
		}

		final long nextFP() throws IOException {
			this.enumRaf.readLongNat(); /* drop */
			return this.enumRaf.readLong();
		}
	}

}
