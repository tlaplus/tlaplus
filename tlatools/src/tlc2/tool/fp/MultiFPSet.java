// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:16:00 PST by lamport
//      modified on Tue May 15 11:44:57 PDT 2001 by yuanyu

package tlc2.tool.fp;

import java.io.IOException;
import java.rmi.NoSuchObjectException;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;

import tlc2.output.EC;
import tlc2.tool.TLCTrace;
import tlc2.util.BufferedRandomAccessFile;
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
	protected FPSet[] sets;

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
		
		this.sets = new FPSet[fpSetConfiguration.getMultiFPSetCnt()];
		
		if (fpMemSize == MEM_DEFAULT) {
			fpMemSize = HeapBasedDiskFPSet.DefaultMaxTblCnt / 20;
		}

		this.sets = getNestedFPSets(fpSetConfiguration);
		this.fpbits = 64 - bits;
	}

	protected FPSet[] getNestedFPSets(final FPSetConfiguration fpSetConfiguration) throws RemoteException {
		int len = fpSetConfiguration.getMultiFPSetCnt();
		final FPSet[] s = new FPSet[len];
		for (int i = 0; i < len; i++) {
			s[i] = FPSetFactory.getFPSet(new MultiFPSetConfiguration(fpSetConfiguration));
		}
		return s;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#init(int, java.lang.String, java.lang.String)
	 */
	public final void init(int numThreads, String metadir, String filename) throws IOException {
		for (int i = 0; i < this.sets.length; i++) {
			this.sets[i].init(numThreads, metadir, filename + "_" + i);
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#size()
	 */
	public final long size() {
		/* Returns the number of fingerprints in this set. */
		long sum = 0;
		for (int i = 0; i < this.sets.length; i++) {
			sum += this.sets[i].size();
		}
		return sum;
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
		return this.sets[idx];
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
		for (int i = 0; i < this.sets.length; i++) {
			this.sets[i].close();
		}
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#unexportObject(boolean)
	 */
	public void unexportObject(boolean force) throws NoSuchObjectException {
		for (int i = 0; i < this.sets.length; i++) {
			this.sets[i].unexportObject(force);
		}
		UnicastRemoteObject.unexportObject(this, force);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#checkFPs()
	 */
	public final double checkFPs() throws IOException {
		/* This is not quite correct. */
		double res = Double.NEGATIVE_INFINITY;
		for (int i = 0; i < this.sets.length; i++) {
			res = Math.max(res, this.sets[i].checkFPs());
		}
		return res;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#exit(boolean)
	 */
	public final void exit(boolean cleanup) throws IOException {
		for (int i = 0; i < this.sets.length; i++) {
			this.sets[i].exit(cleanup);
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#beginChkpt()
	 */
	public final void beginChkpt() throws IOException {
		for (int i = 0; i < this.sets.length; i++) {
			this.sets[i].beginChkpt();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#commitChkpt()
	 */
	public final void commitChkpt() throws IOException {
		for (int i = 0; i < this.sets.length; i++) {
			this.sets[i].commitChkpt();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#recover()
	 */
	public final void recover() throws IOException {
		for (int i = 0; i < this.sets.length; i++) {
			this.sets[i].prepareRecovery();
		}

		long recoverPtr = TLCTrace.getRecoverPtr();
		BufferedRandomAccessFile braf = new BufferedRandomAccessFile(TLCTrace.getFilename(), "r");
		while (braf.getFilePointer() < recoverPtr) {
			braf.readLongNat(); /* drop */
			long fp = braf.readLong();
			getFPSet(fp).recoverFP(fp);
		}

		for (int i = 0; i < this.sets.length; i++) {
			this.sets[i].completeRecovery();
		}
	}

	/* (non-Javadoc)
	 * 
	 * NOOP!
	 * 
	 * @see tlc2.tool.fp.FPSet#prepareRecovery()
	 */
	public final void prepareRecovery() throws IOException { /* SKIP */
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#recoverFP(long)
	 */
	public final void recoverFP(long fp) throws IOException {
		Assert.check(!this.put(fp), EC.TLC_FP_NOT_IN_SET);
	}

	/* (non-Javadoc)
	 * 
	 * NOOP!
	 * 
	 * @see tlc2.tool.fp.FPSet#completeRecovery()
	 */
	public final void completeRecovery() throws IOException { /* SKIP */
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#beginChkpt(java.lang.String)
	 */
	public final void beginChkpt(String filename) throws IOException {
		for (int i = 0; i < this.sets.length; i++) {
			this.sets[i].beginChkpt(filename + "_" + i);
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#commitChkpt(java.lang.String)
	 */
	public final void commitChkpt(String filename) throws IOException {
		for (int i = 0; i < this.sets.length; i++) {
			this.sets[i].commitChkpt(filename + "_" + i);
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSet#recover(java.lang.String)
	 */
	public final void recover(String filename) throws IOException {
		for (int i = 0; i < this.sets.length; i++) {
			this.sets[i].recover(filename + "_" + i);
		}
	}

	public FPSet[] getFPSets() {
		return sets;
	}
}
