// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

import java.io.EOFException;
import java.io.IOException;
import java.io.RandomAccessFile;
import java.rmi.RemoteException;
import java.util.Arrays;

import tlc2.output.EC;
import util.Assert;

@SuppressWarnings("serial")
public class LSBDiskFPSet extends HeapBasedDiskFPSet {

	protected LSBDiskFPSet(final FPSetConfiguration fpSetConfig) throws RemoteException {
		super(fpSetConfig);
		this.flusher = new LSBFlusher();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.DiskFPSet#getAuxiliaryStorageRequirement()
	 */
	protected double getAuxiliaryStorageRequirement() {
		return 2.5d;
	}
	
	public class LSBFlusher extends Flusher {

		private long[] buff;
		
		/* (non-Javadoc)
		 * @see tlc2.tool.fp.DiskFPSet.Flusher#prepareTable()
		 */
		@Override
		protected void prepareTable() {
			// Verify tblCnt is still within positive Integer.MAX_VALUE bounds
			int cnt = (int) tblCnt.get();
			Assert.check(cnt > 0, EC.GENERAL);
			
			// copy table contents into a buffer array buff; do not erase tbl
			buff = new long[cnt];
			int idx = 0;
			for (int j = 0; j < tbl.length; j++) {
				long[] bucket = tbl[j];
				if (bucket != null) {
					int blen = bucket.length;
					// for all bucket positions and non-null values
					for (int k = 0; k < blen && bucket[k] > 0; k++) {
						buff[idx++] = bucket[k];
						// indicate fp has been flushed to disk
						bucket[k] |= 0x8000000000000000L;
					}
				}
			}
			
			// sort in-memory entries
			Arrays.sort(buff, 0, buff.length);
		}

		/* (non-Javadoc)
		 * @see tlc2.tool.fp.DiskFPSet.Flusher#mergeNewEntries(java.io.RandomAccessFile, java.io.RandomAccessFile)
		 */
		@Override
		protected void mergeNewEntries(RandomAccessFile inRAF, RandomAccessFile outRAF) throws IOException {
			final int buffLen = buff.length;

			// Precompute the maximum value of the new file
			long maxVal = buff[buffLen - 1];
			if (index != null) {
				maxVal = Math.max(maxVal, index[index.length - 1]);
			}

			int indexLen = calculateIndexLen(buffLen);
			index = new long[indexLen];
			index[indexLen - 1] = maxVal;
			currIndex = 0;
			counter = 0;

			// initialize positions in "buff" and "inRAF"
			int i = 0;
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
			while (!eof && i < buffLen) {
				if (value < buff[i]) {
					writeFP(outRAF, value);
					try {
						value = inRAF.readLong();
					} catch (EOFException e) {
						eof = true;
					}
				} else {
					// prevent converting every long to String when assertion holds (this is expensive)
					if(value == buff[i]) {
						Assert.check(false, EC.TLC_FP_VALUE_ALREADY_ON_DISK,
								String.valueOf(value));
					}
					writeFP(outRAF, buff[i++]);
				}
			}

			// write elements of remaining list
			if (eof) {
				while (i < buffLen) {
					writeFP(outRAF, buff[i++]);
				}
			} else {
				do {
					writeFP(outRAF, value);
					try {
						value = inRAF.readLong();
					} catch (EOFException e) {
						eof = true;
					}
				} while (!eof);
			}
			Assert.check(currIndex == indexLen - 1, EC.SYSTEM_INDEX_ERROR);

			// maintain object invariants
			fileCnt += buffLen;
		}
	}
}
