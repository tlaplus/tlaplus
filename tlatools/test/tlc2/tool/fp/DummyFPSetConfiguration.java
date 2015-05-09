// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

@SuppressWarnings("serial")
public class DummyFPSetConfiguration extends FPSetConfiguration {
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.FPSetConfiguration#getMemoryInBytes()
	 */
	public long getMemoryInBytes() {
		// Override super.getMemoryInBytes() to allow unit tests to pass an
		// explicit value by bypassing util.TLCRuntime.getFPMemSize(double).
		// getFPMemSize(double) sets a lower limit for the DiskFPSet size, 
		// which unit tests might have to tear down.
		return memoryInBytes;
	}
	
	public void setMemoryInFingerprintCnt(int numberOfFingerprints) {
		this.memoryInBytes = numberOfFingerprints * FPSet.LongSize;
	}
}
