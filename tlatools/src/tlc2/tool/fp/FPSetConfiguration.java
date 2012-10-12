// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp;

import java.io.Serializable;

@SuppressWarnings("serial")
public class FPSetConfiguration implements Serializable {
	
	private long memoryInBytes;
	private int fpBits = 0;

	public FPSetConfiguration() {
		this(-1);
	}
	
	/**
	 * @param memoryInBytes Memory dedicate to _all_ {@link FPSet} in Bytes!!!
	 */
	public FPSetConfiguration(final long memoryInBytes) {
		this.memoryInBytes = memoryInBytes;
	}

	/**
	 * @return the memoryInBytes
	 */
	public long getMemoryInBytes() {
		return memoryInBytes;
	}
	
	public long getMemoryInFingerprintCnt() {
		//TODO Replace FPSet.LongSize with fingerprint length
		return memoryInBytes / FPSet.LongSize;
	}

	public void setFpBits(int fpBits) {
		this.fpBits = fpBits;
	}
	
	/**
	 * @return the fpBits
	 */
	public int getFpBits() {
		return fpBits;
	}

	public int getMultiFPSetCnt() {
		return 1 << fpBits;
	}
	
	public int getPrefixBits() {
		return fpBits;
	}

	public void setMemory(long fpMemSize) {
		this.memoryInBytes = fpMemSize;
	}
}
