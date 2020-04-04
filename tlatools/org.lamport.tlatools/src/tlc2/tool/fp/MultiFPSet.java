// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:16:00 PST by lamport
//      modified on Tue May 15 11:44:57 PDT 2001 by yuanyu

package tlc2.tool.fp;

import java.io.IOException;
import java.rmi.NoSuchObjectException;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.IntStream;

import tlc2.output.EC;
import tlc2.tool.TLCTrace;
import tlc2.tool.TLCTrace.Enumerator;
import util.Assert;

/**
 * An <code>MultiFPSet</code> is a set of 64-bit fingerprints.
 */
@SuppressWarnings("serial")
public class MultiFPSet extends FPSet {

	/**
	 * Indicates that child {@link FPSet} should allocate the built-in amount of memory
	 */
	private static final int MEM_DEFAULT = -1;

	public static final int MAX_FPBITS = 30;
	public static final int MIN_FPBITS = 0;

	/**
	 * Contains all nested {@link FPSet}s 
	 */
	protected final List<FPSet> sets;

	/**
	 * Amount of leftmost bits used to determine nested {@link FPSet}
	 */
	protected int fpbits;

	/**
	 * Create a MultiFPSet with 2^bits FPSets.
	 * @param bits [1,30]
	 */
	public MultiFPSet(final FPSetConfiguration fpSetConfiguration) throws RemoteException {
		super(fpSetConfiguration);

		int bits = fpSetConfiguration.getFpBits();
		long fpMemSize = fpSetConfiguration.getMemoryInBytes();
		
	    // LL modified error message on 7 April 2012
		Assert.check(bits > 0 && bits <= MAX_FPBITS, "Illegal number of FPSets found.");
		
		if (fpMemSize == MEM_DEFAULT) {
			fpMemSize = HeapBasedDiskFPSet.DefaultMaxTblCnt / 20;
		}

		this.sets = getNestedFPSets(fpSetConfiguration);
		this.fpbits = 64 - bits;
	}

	protected List<FPSet> getNestedFPSets(final FPSetConfiguration fpSetConfiguration) throws RemoteException {
		final List<FPSet> s = new ArrayList<>(fpSetConfiguration.getMultiFPSetCnt());
		for (int i = 0; i < fpSetConfiguration.getMultiFPSetCnt(); i++) {
			s.add(FPSetFactory.getFPSet(new MultiFPSetConfiguration(fpSetConfiguration)));
		}
		return s;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#init(int, java.lang.String, java.lang.String)
	 */
	public final FPSet init(final int numThreads, final String metadir, final String filename) throws IOException {
		IntStream.range(0, this.sets.size()).parallel().forEach(i -> {
			try {
				sets.get(i).init(numThreads, metadir, filename + "_" + i);
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		});
		return this;
	}

	
	@Override
	public void incWorkers(final int num) {
		sets.stream().forEach(s -> s.incWorkers(num) );
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#size()
	 */
	public final long size() {
		/* Returns the number of fingerprints in this set. */
		return sets.parallelStream().mapToLong(FPSet::size).sum();
	}
	
	/**
	 * @param fp
	 * @return Partition given fp into the {@link FPSet} space 
	 */
	protected FPSet getFPSet(long fp) {
		// determine corresponding fpset (using unsigned right shift)
		// shifts a zero into the leftmost (msb) position of the first operand for right operand times
		// and cast it to int loosing the leftmost 32 bit
		final int idx = (int) (fp >>> this.fpbits);
		return this.sets.get(idx);
	}

	/**
	 * Returns <code>true</code> iff the fingerprint <code>fp</code> is in this
	 * set. If the fingerprint is not in the set, it is added to the set as a
	 * side-effect.
	 * 
	 * @see tlc2.tool.fp.FPSet#put(long)
	 */
	public final boolean put(long fp) throws IOException {
		return getFPSet(fp).put(fp);
	}

	/**
	 * Returns <code>true</code> iff the fingerprint <code>fp</code> is in this
	 * set.
	 * 
	 * @see tlc2.tool.fp.FPSet#contains(long)
	 */
	public final boolean contains(long fp) throws IOException {
		return getFPSet(fp).contains(fp);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#close()
	 */
	public final void close() {
		for (FPSet fpSet : sets) {
			fpSet.close();
		}
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#unexportObject(boolean)
	 */
	public void unexportObject(boolean force) throws NoSuchObjectException {
		for (FPSet fpSet : sets) {
			fpSet.unexportObject(force);
		}
		UnicastRemoteObject.unexportObject(this, force);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#checkFPs()
	 */
	public final long checkFPs() throws IOException {
		return sets.parallelStream().mapToLong(s -> {
			try {
				return s.checkFPs();
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		}).min().orElse(Long.MAX_VALUE);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#checkInvariant()
	 */
	public boolean checkInvariant() throws IOException {
		return sets.parallelStream().allMatch(s -> {
			try {
				return s.checkInvariant();
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		});
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#exit(boolean)
	 */
	public final void exit(boolean cleanup) throws IOException {
	    super.exit(cleanup);
		for (FPSet fpSet : sets) {
			fpSet.exit(cleanup);
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#beginChkpt()
	 */
	public final void beginChkpt() throws IOException {
		for (FPSet fpSet : sets) {
			fpSet.beginChkpt();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#commitChkpt()
	 */
	public final void commitChkpt() throws IOException {
		for (FPSet fpSet : sets) {
			fpSet.commitChkpt();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#recover()
	 */
	public final void recover(TLCTrace trace) throws IOException {
		final Enumerator elements = trace.elements();
		while (elements.nextPos() != -1) {
			long fp = elements.nextFP();
			getFPSet(fp).recoverFP(fp);
		}
		elements.close();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#recoverFP(long)
	 */
	public final void recoverFP(long fp) throws IOException {
		Assert.check(!this.put(fp), EC.TLC_FP_NOT_IN_SET);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#beginChkpt(java.lang.String)
	 */
	public final void beginChkpt(String filename) throws IOException {
		IntStream.range(0, this.sets.size()).parallel().forEach(i -> {
			try {
				sets.get(i).beginChkpt(filename + "_" + i);
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		});
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#commitChkpt(java.lang.String)
	 */
	public final void commitChkpt(String filename) throws IOException {
		IntStream.range(0, this.sets.size()).parallel().forEach(i -> {
			try {
				sets.get(i).commitChkpt(filename + "_" + i);
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		});
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#recover(java.lang.String)
	 */
	public final void recover(String filename) throws IOException {
		IntStream.range(0, this.sets.size()).parallel().forEach(i -> {
			try {
				sets.get(i).recover(filename + "_" + i);
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		});
	}

	public FPSet[] getFPSets() {
		return sets.toArray(new FPSet[sets.size()]);
	}
}
