// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

@SuppressWarnings("serial")
class MultiFPSetConfiguration extends FPSetConfiguration {

	public MultiFPSetConfiguration(final FPSetConfiguration fpSetConfig) {
		// Do not use getter method as it does not necessarily return the member
		// value
		this.memoryInBytes = fpSetConfig.memoryInBytes;
		// Set wrapper to values of config to be wrapped
		this.fpBits = fpSetConfig.getFpBits();
		this.ratio = fpSetConfig.getRatio();
		
		// Sanity check configuration right away
		if (getMemoryInFingerprintCnt() <= 0) {
			throw new IllegalArgumentException(
					"Given fpSetConfig results in zero or negative fp count.");
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSetConfiguration#allowsNesting()
	 */
	public boolean allowsNesting() {
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSetConfiguration#getMemoryInBytes()
	 */
	public long getMemoryInBytes() {
		return super.getMemoryInBytes() / getMultiFPSetCnt();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSetConfiguration#getMemoryInFingerprintCnt()
	 */
	public long getMemoryInFingerprintCnt() {
		return super.getMemoryInFingerprintCnt() / getMultiFPSetCnt();
	}
}