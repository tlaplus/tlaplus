// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.EOFException;
import java.io.File;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.rmi.RemoteException;
import java.util.Arrays;
import java.util.NoSuchElementException;

import tlc2.output.EC;
import tlc2.util.BufferedRandomAccessFile;
import util.Assert;

@SuppressWarnings("serial")
public class MSBDiskFPSet extends DiskFPSet {

	/**
	 * Number of bits to right shift bits during index calculation
	 */
	protected final int moveBy;

	/**
	 * Construct a new <code>DiskFPSet2</code> object whose internal memory
	 * buffer of new fingerprints can contain up to
	 * <code>DefaultMaxTblCnt</code> entries. When the buffer fills up, its
	 * entries are atomically flushed to the FPSet's backing disk file.
	 * 
	 * @param maxInMemoryCapacity The number of fingerprints (not memory) this DiskFPSet should maximally store in-memory.
	 * @throws RemoteException
	 */
	protected MSBDiskFPSet(long maxInMemoryCapacity) throws RemoteException {
		this(maxInMemoryCapacity, 0);
	}
	
	/**
	 * Construct a new <code>DiskFPSet2</code> object whose internal memory
	 * buffer of new fingerprints can contain up to
	 * <code>DefaultMaxTblCnt</code> entries. When the buffer fills up, its
	 * entries are atomically flushed to the FPSet's backing disk file.
	 * 
	 * @param maxInMemoryCapacity The number of fingerprints (not memory) this DiskFPSet should maximally store in-memory.
	 * @param preBits Take the amount of DiskFPSet instance into account to move the index bits further to the right
	 * @throws RemoteException
	 */
	protected MSBDiskFPSet(long maxInMemoryCapacity, int preBits) throws RemoteException {
		super(maxInMemoryCapacity);

		// To pre-sort fingerprints in memory, use n MSB fp bits for the
		// index. However, we cannot use the 31 bit, because it is used to
		// indicate if a fp has been flushed to disk. Hence we use the first n
		// bits starting from the second most significant bit.
		this.moveBy = (31 - preBits) - (logMaxMemCnt - LogMaxLoad);
		this.mask = (capacity - 1) << moveBy;
	}


	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#getAuxiliaryStorageRequirement()
	 */
	@Override
	protected double getAuxiliaryStorageRequirement() {
		return 1.5;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#getIndex(long)
	 */
	@Override
	protected int getIndex(final long fp) {
		// calculate hash value (just n most significant bits of fp) which is
		// used as an index address
		return ((int) (fp >>> 32) & this.mask) >> moveBy;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#flushTable()
	 */
	@Override
	void flushTable() throws IOException {
		if (this.tblCnt == 0)
			return;

		System.out.println("Flushing disk for the n-time: " + getGrowDiskMark());

		// Why not sort this.tbl in-place rather than doubling memory
		// requirements by copying to clone array and subsequently sorting it?
		// - disk written fps are marked disk written by changing msb to 1
		// - next time such a fp from the in-memory this.tlb is converted on the
		// fly back and again used to do an in-memory lookup
		//
		// - this.tbl bucket assignment (hashing) is done on least significant bits,
		// which makes in-place sort with overlay index infeasible
		// - erasing this.tbl means we will loose the in-memory cache completely until it fills up again
		// - new fps overwrite disk flushed fps in-memory

		// copy table contents into a buffer array buff; do not erase tbl, but 1
		// msb of each fp to indicate it has been flushed to disk
		for (int j = 0; j < this.tbl.length; j++) {
			long[] bucket = this.tbl[j];
			if (bucket != null) {
				int blen = bucket.length;
				// for all bucket positions and non-null values
				int k = 0;
				for (; k < blen && bucket[k] > 0; k++) {
					continue;
				}
				// * Postconditions:
				// * - Zero/0 Element(s) remains at the end
				// * - Negative elements maintain their position (remain untouched) 
				Arrays.sort(bucket, 0, k);
			}
		}

		// At this point this.tbl should be fully sorted modulo the fps which
		// had been flush in a previous flush operation and zero/0 (which is invalid anyway).


		// merge array with disk file
		try {
			this.mergeNewEntries(this.tbl, this.tblCnt);
		} catch (IOException e) {
			String msg = "Error: merging entries into file "
					+ this.fpFilename + "  " + e;
			throw new IOException(msg);
		}

		this.tblCnt = 0;
		this.bucketsCapacity = 0;
		this.tblLoad = 0;
		// // reset statistic counters
		// this.memHitCnt = 0;
		//
		// this.diskHitCnt = 0;
		// this.diskWriteCnt = 0;
		// this.diskSeekCnt = 0;
		// this.diskLookupCnt = 0;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#mergeNewEntries(long[])
	 * 
	 * NOTE: This is (supposed to be) an almost exact clone of
	 * tlc2.tool.fp.DiskFPSet.mergeNewEntries(long[]) except for the in params
	 * and the nested tlc2.tool.fp.MSBDiskFPSet.mergeNewEntries(long[][], int,
	 * RandomAccessFile, RandomAccessFile) call.
	 */
	private final void mergeNewEntries(long[][] buff, int buffLen
			) throws IOException {
		// Implementation Note: Unfortunately, because the RandomAccessFile
		// class (and hence, the BufferedRandomAccessFile class) does not
		// provide a way to re-use an existing RandomAccessFile object on
		// a different file, this implementation must close all existing
		// files and re-allocate new BufferedRandomAccessFile objects.

		// close existing files (except brafPool[0])
		for (int i = 0; i < this.braf.length; i++) {
			this.braf[i].close();
		}
		for (int i = 1; i < this.brafPool.length; i++) {
			this.brafPool[i].close();
		}

		// create temporary file
		File tmpFile = new File(tmpFilename);
		tmpFile.delete();
		RandomAccessFile tmpRAF = new BufferedRandomAccessFile(tmpFile, "rw");
		RandomAccessFile raf = this.brafPool[0];
		raf.seek(0);

		// merge
		this.mergeNewEntries(buff, buffLen, raf, tmpRAF);

		// clean up
		raf.close();
		tmpRAF.close();
		String realName = this.fpFilename;
		File currFile = new File(realName);
		currFile.delete();
		boolean status = tmpFile.renameTo(currFile);
		Assert.check(status, EC.SYSTEM_UNABLE_NOT_RENAME_FILE);

		// reopen a BufferedRAF for each thread
		for (int i = 0; i < this.braf.length; i++) {
			// Better way would be to provide method BRAF.open
			this.braf[i] = new BufferedRandomAccessFile(realName, "r");
		}
		for (int i = 0; i < this.brafPool.length; i++) {
			// Better way would be to provide method BRAF.open
			this.brafPool[i] = new BufferedRandomAccessFile(realName, "r");
		}
		this.poolIndex = 0;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#mergeNewEntries(long[], int, java.io.RandomAccessFile, java.io.RandomAccessFile)
	 */
	private final void mergeNewEntries(long[][] buff, int buffLen,
			RandomAccessFile inRAF, RandomAccessFile outRAF) throws IOException {

		final TLCIterator itr = new TLCIterator(buff);

		// Precompute the maximum value of the new file
		long maxVal = itr.getLast();
		if (this.index != null) {
			maxVal = Math.max(maxVal, this.index[this.index.length - 1]);
		}

		int indexLen = (int) ((this.fileCnt + buffLen - 1) / NumEntriesPerPage) + 2;
		this.index = new long[indexLen];
		this.index[indexLen - 1] = maxVal;
		this.currIndex = 0;
		this.counter = 0;

		// initialize positions in "buff" and "inRAF"
		long value = 0L; // initialize only to make compiler happy
		boolean eof = false;
		if (this.fileCnt > 0) {
			try {
				value = inRAF.readLong();
			} catch (EOFException e) {
				eof = true;
			}
		} else {
			eof = true;
		}

		// merge while both lists still have elements remaining
		long fp = itr.next();
		while (!eof) {
			if (value < fp || !itr.hasNext()) { // check for itr.hasNext() here to write last value when itr is used up.
				this.writeFP(outRAF, value);
				try {
					value = inRAF.readLong();
				} catch (EOFException e) {
					eof = true;
				}
			} else {
				// prevent converting every long to String when assertion holds (this is expensive)
				if (value == fp) {
					Assert.check(false, EC.TLC_FP_VALUE_ALREADY_ON_DISK,
							String.valueOf(value));
				}
				this.writeFP(outRAF, fp);
				// we used on fp up, thus move to next one
				fp = itr.next();
			}
		}

		// write elements of remaining list
		if (eof) {
			while (fp > 0L) {
				this.writeFP(outRAF, fp);
				if (!itr.hasNext()) {
					break;
				}
				fp = itr.next();
			}
		} else {
			do {
				this.writeFP(outRAF, value);
				try {
					value = inRAF.readLong();
				} catch (EOFException e) {
					eof = true;
				}
			} while (!eof);
		}
		Assert.check(itr.reads() == buffLen, EC.GENERAL);

		// currIndex is amount of disk writes
		Assert.check(this.currIndex == indexLen - 1, EC.SYSTEM_INDEX_ERROR);

		// maintain object invariants
		this.fileCnt += buffLen;
	}
	
	/**
	 *
	 */
	public static class TLCIterator {
		/**
		 * The underlying buffer this {@link TLCIterator} is iterating on.
		 */
		private final long[][] buff;
		/**
		 * Index pointing to the current bucket in the first level of
		 * {@link TLCIterator#buff}
		 */
		private int firstIdx = 0;
		/**
		 * Index pointing to the current element in the current bucket which is the
		 * second level of {@link TLCIterator#buff}
		 */
		private int secondIdx = 0;
		/**
		 * Used to verify that the elements we hand out are strictly monotonic
		 * increasing.
		 */
		private long previous = -1l;
		/**
		 * Number of elements read with next()
		 */
		private long readElements = 0L;

		/**
		 * @param buff an [][] with null elements on the second level.
		 */
		public TLCIterator(final long[][] buff) {
			this.buff = buff;
		}

	    /**
	     * Returns <tt>true</tt> if the iteration has more elements. (In other
	     * words, returns <tt>true</tt> if <tt>next</tt> would return an element
	     * rather than throwing an exception.)
	     *
	     * @return <tt>true</tt> if the iterator has more elements.
	     */
		public boolean hasNext() {
			// hasNext does not move the indices at all!
			
			// firstIdx within buff[].length
			if (firstIdx < buff.length) {
				long[] bucket = buff[firstIdx];
				// secondIdx within bucket[].length and with valid elements in current bucket 
				if (bucket != null && secondIdx < bucket.length && bucket[secondIdx] > 0) {
					return true;
				// we might have reached a null or negative range in buff[] -> skip it until
				// we reach a non-null and non negative bucket or we get to the end of buff[]
				} else {
					for (int i = firstIdx + 1; i < buff.length; i++) {
						if (buff[i] != null && buff[i].length > 0 && buff[i][0] > 0) {
							return true;
						}
					}
				}
			}
			return false;
		}

	    /**
	     * Returns the next element in the iteration.
	     *
	     * @return the next element in the iteration.
	     * @exception NoSuchElementException iteration has no more elements.
	     */
		public long next() {
			long result = -1l;
			
			// at least one more element in current bucket
			if (firstIdx < buff.length) {
				long[] bucket = buff[firstIdx];
				if (bucket != null && secondIdx < bucket.length && bucket[secondIdx] > 0) {
					result = bucket[secondIdx];
					bucket[secondIdx] |= 0x8000000000000000L;
					secondIdx++;
				} else {
					for (int i = firstIdx + 1; i < buff.length && result == -1L; i++) {
						if (buff[i] != null && buff[i].length > 0 && buff[i][0] > 0) {
							firstIdx = i;
							secondIdx = 0;
							result = buff[firstIdx][secondIdx];
							buff[firstIdx][secondIdx] |= 0x8000000000000000L;
							secondIdx++;
							break; // redundant to "result == -1L" in for loop
						}
					}
				}
			}
			
			// adhere to the general Iterator contract to fail fast and not hand out
			// meaningless values
			if (result == -1L) {
				throw new NoSuchElementException();
			}
			
			// hand out strictly monotonic increasing elements
			Assert.check(previous < result, EC.GENERAL);
			previous = result;
			
			// maintain read statistics
			readElements++;
			
			return result;
		}

		/**
		 * @return The last element in the iteration.
	     * @exception NoSuchElementException if iteration is empty.
		 */
		public long getLast() {
			int len = buff.length - 1;
			long[] bucket = buff[len];

			// find last bucket containing elements, buff elements might be null if
			// no fingerprint for such an index has been added to the DiskFPSet
			while (bucket == null) {
				bucket = buff[--len];
			}
			
			// find last element > 0 in bucket
			for (int i = bucket.length - 1; i >= 0 ;i--) {
				if (bucket[i] > 0) {
					return bucket[i];
				}
			}
			throw new NoSuchElementException();
		}
		
		/**
		 * @return The number of element read with {@link TLCIterator#next()} since
		 *         the creation of this instance.
		 */
		public long reads() {
			return readElements;
		}
	}
}
