// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.

package tlc2.tool.fp;

import java.io.EOFException;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.rmi.RemoteException;
import java.util.Arrays;
import java.util.NoSuchElementException;

import tlc2.output.EC;
import util.Assert;

@SuppressWarnings("serial")
public class MSBDiskFPSet extends HeapBasedDiskFPSet {

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
	 * @param preBits Take the amount of DiskFPSet instance into account to move the index bits further to the right
	 * @throws RemoteException
	 */
	protected MSBDiskFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
		super(fpSetConfig);

		// To pre-sort fingerprints in memory, use n MSB fp bits for the
		// index. However, we cannot use the 32st bit, because it is used to
		// indicate if a fp has been flushed to disk. Hence we use the first n
		// bits starting from the second most significant bit.
		this.moveBy = (31 - fpSetConfig.getPrefixBits()) - (logMaxMemCnt - LogMaxLoad);
		this.mask = (capacity - 1) << moveBy;
		
		this.flusher = new MSBFlusher();
	}


	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#getAuxiliaryStorageRequirement()
	 */
	@Override
	protected double getAuxiliaryStorageRequirement() {
		// Need auxiliary storage for the disk file index which needs approx.
		// 1/3 of the overall memory.
		return 1.5d;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#index(long, int)
	 */
	@Override
	protected long index(long fp, long aMask) {
		// calculate hash value (just n most significant bits of fp) which is
		// used as an index address
		return ((int) (fp >>> 32) & aMask) >> moveBy;
	}
	
	public class MSBFlusher extends Flusher {

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.DiskFPSet.Flusher#preFlushTable()
		 */
		protected void prepareTable() {
			
			// copy table contents into a buffer array buff; do not erase tbl, but 1
			// msb of each fp to indicate it has been flushed to disk
			for (int j = 0; j < tbl.length; j++) {
				long[] bucket = tbl[j];
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
		}
		
		/* (non-Javadoc)
		 * @see tlc2.tool.fp.DiskFPSet#mergeNewEntries(long[], int, java.io.RandomAccessFile, java.io.RandomAccessFile)
		 */
		protected void mergeNewEntries(RandomAccessFile inRAF, RandomAccessFile outRAF) throws IOException {
			final long buffLen = tblCnt.get();
			final TLCIterator itr = new TLCIterator(tbl);

			// Precompute the maximum value of the new file.
			// If this isn't the first merge, the index has
			// the last element of the disk file. In that case
			// the new maxVal is the larger element of the two
			// in-memory and on-disk elements.
			// The largest on-disk element is passed to the
			// iterator as a lower bound.
			long maxVal;
			if (index != null) {
				maxVal = itr.getLast(index[index.length - 1]);
			} else {
				maxVal = itr.getLast();
			}
	
			int indexLen = calculateIndexLen(buffLen);
			index = new long[indexLen];
			index[indexLen - 1] = maxVal;
			currIndex = 0;
			counter = 0;
	
			// initialize positions in "buff" and "inRAF"
			long value = 0L; // initialize only to make compiler happy
			boolean eof = false;
			if (fileCnt > 0) {
				try {
					value = inRAF.readLong();
				} catch (EOFException e) {
					eof = true;
				}
			} else {
				eof = true;
			}
	
			// merge while both lists still have elements remaining
			boolean eol = false;
			long fp = itr.next();
			while (!eof || !eol) {
				if ((value < fp || eol) && !eof) {
					writeFP(outRAF, value);
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
					writeFP(outRAF, fp);
					// we used one fp up, thus move to next one
					try {
						fp = itr.next();
					} catch (NoSuchElementException e) {
						// has read all elements?
						Assert.check(!itr.hasNext(), EC.GENERAL);
						Assert.check(itr.reads() == buffLen, EC.GENERAL);
						eol = true;
					}
				}
			}
			
			// both sets used up completely
			Assert.check(eof && eol, EC.GENERAL);
	
			// currIndex is amount of disk writes
			Assert.check(currIndex == indexLen - 1, EC.SYSTEM_INDEX_ERROR);
	
			// maintain object invariants
			fileCnt += buffLen;
		}
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
		 * @param lowBound
		 *            Stop searching for the last element if no element is
		 *            larger than lowBound
		 * @return The last element in the iteration that is larger than lowBound
		 * @exception NoSuchElementException
		 *                if iteration is empty.
		 *                <p>
		 *                Pre-condition: Each bucket is sorted in ascending
		 *                order. on-disk fingerprints don't adhere to the
		 *                ascending order though!
		 */
		public long getLast(final long lowBound) {
			int len = buff.length - 1;
			long[] bucket = buff[len];

			// Walk from the end of buff to the beginning. Each bucket that is
			// found and non-null (null if no fingerprint for such an index has
			// been added to the DiskFPSet) is checked for a valid fingerprint.
			// A fp is valid iff it is larger zero. A zero fingerprint slot
			// indicates an unoccupied slot, while a negative one corresponds to
			// a fp that has already been flushed to disk.
			while (len > 0) {
				bucket = buff[--len];

				// Find last element > 0 in bucket (negative elements have already
				// been flushed to disk, zero indicates an unoccupied slot).
				if (bucket != null) {
					for (int i = bucket.length - 1; i >= 0; i--) {
						final long fp = bucket[i];
						// unused slot
						if (fp == 0) {
							continue;
						}
						// in-memory fingerprint
						if (fp > 0) {
							if (fp < lowBound) {
								// smaller lowBound
								return lowBound;
							} else {
								// larger or equal lowBound
								return fp;
							}
						}
						// Cannot take on-disk fingerprints (negative ones) into
						// account. They don't adhere to the precondition that
						// the bucket is sorted. The bucket is logically sorted
						// only for in-memory fingerprints.
					}
				}
			}
			// At this point we have scanned the complete buff, but haven't
			// found a single fingerprint that hasn't been flushed to disk
			// already.
			throw new NoSuchElementException();
		}

		/**
		 * @return The last element in the iteration.
	     * @exception NoSuchElementException if iteration is empty.
	     * 
	     * Pre-condition: Each bucket is sorted in ascending order!
		 */
		public long getLast() {
			/*
			 * Tempting to delegate to getLast(Long.MAX_VALUE). However,
			 * getLast() could not throw a NoSuchElementException when the
			 * value returned is Long.MAX_VALUE. It could be a valid value, but
			 * it might as well be the cutOff.
			 */
			
			int len = buff.length - 1;
			long[] bucket = buff[len];

			// Walk from the end of buff to the beginning. Each bucket that is
			// found and non-null (null if no fingerprint for such an index has
			// been added to the DiskFPSet) is checked for a valid fingerprint.
			// A fp is valid iff it is larger zero. A zero fingerprint slot
			// indicates an unoccupied slot, while a negative one corresponds to
			// a fp that has already been flushed to disk.
			while (len > 0) {
				bucket = buff[--len];

				// Find last element > 0 in bucket (negative elements have already
				// been flushed to disk, zero indicates an unoccupied slot).
				if (bucket != null) {
					for (int i = bucket.length - 1; i >= 0; i--) {
						if (bucket[i] > 0) {
							return bucket[i];
						}
					}
				}
			}
			// At this point we have scanned the complete buff, but haven't
			// found a single fingerprint that hasn't been flushed to disk
			// already.
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
