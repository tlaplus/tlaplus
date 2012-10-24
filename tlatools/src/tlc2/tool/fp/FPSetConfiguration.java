// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.Serializable;

import tlc2.output.EC;
import util.Assert;
import util.TLCRuntime;

@SuppressWarnings("serial")
public class FPSetConfiguration implements Serializable {
	
	protected int fpBits = 0;
	protected long memoryInBytes = -1L;
	protected double ratio;
	protected String implementation;

	public FPSetConfiguration() {
		// By default allocate 25% of memory for fingerprint storage
		this(.25d);
	}
	
	public FPSetConfiguration(Double aRatio) {
		this.ratio = aRatio;
		// Read the implementation class from the System properties instead of
		// the cmd line. Right now I'm reluctant to expose the impl class as a 
		// cmd line parameter and carry it forth forever.
		this.implementation = System.getProperty(FPSetFactory.IMPL_PROPERTY,
				FPSetFactory.getImplementationDefault());
	}

	public boolean allowsNesting() {
		return getFpBits() > 0;
	}
	
	public int getFpBits() {
		return fpBits;
	}

	public long getMemoryInBytes() {
		final TLCRuntime instance = TLCRuntime.getInstance();
		
		// Here the user has given a ratio of available memory to 
		// use for fingerprint storage
		if (FPSetFactory.allocatesOnHeap(implementation)) {
			// If a user has set memory explicitly, we pass this value to 
			// getFPMemSize(double) which sanitizes the value.
			if (memoryInBytes > 0) {
				return instance.getFPMemSize(memoryInBytes * ratio);
			} else {
				return instance.getFPMemSize(ratio);
			}
		} else {
			// Right now the only consumer of non-heap memory is fingerprint
			// storage. Thus, it makes little sense to allocate less than
			// all non-heap memory dedicated to the VM process. Until this changes,
			// we override ratio to devote all non-heap mem to fingerprint storage.
			//
			// TODO Respect ratio once other TLC data structures start using
			// non-heap memory
			return (long) (instance.getNonHeapPhysicalMemory()/* *ratio */);
		}
	}
	
	public long getMemoryInFingerprintCnt() {
		//TODO Replace FPSet.LongSize with fingerprint length
		
		// Explicitly floor to indicate that an FPSet cannot store a portion of a fingerprint.
		return (long) Math.floor(getMemoryInBytes() / FPSet.LongSize);
	}

	public int getMultiFPSetCnt() {
		return 1 << getFpBits();
	}
	
	public int getPrefixBits() {
		return getFpBits();
	}
	
	public void setRatio(double aRatio) {
		// Allowing aRatio to be 0.0 makes little sense semantically, but we
		// accept it anyway and let TLCRuntime deal with it.
		Assert.check(aRatio >= 0 && aRatio <= 1, EC.GENERAL);
		this.ratio = aRatio;
	}

	public void setFpBits(int fpBits) {
		Assert.check(FPSet.isValid(fpBits), EC.GENERAL);
		this.fpBits = fpBits;
	}

	public double getRatio() {
		return ratio;
	}

	/**
	 * @deprecated DO NOT USE, will be removed once -fpmem cmd line parameter
	 *             only accepts a ratio rather than an absolute memory value
	 * @param fpMemSize
	 */
	public void setMemory(long fpMemSize) {
		Assert.check(fpMemSize >= 0, EC.GENERAL);
		this.memoryInBytes = fpMemSize;
	}
	
	public String getImplementation() {
		return implementation;
	}
}
