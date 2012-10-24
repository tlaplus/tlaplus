// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.util;

import java.text.DecimalFormat;

public class SimpleCache implements Cache {

	private volatile long cacheHit = 1L;
	private volatile long cacheMiss = 1L;
	
	private final long mask;
	private final long[] cache;
	
	/**
	 * A {@link SimpleCache} with room for 2^10 (1024) fingerprints
	 */
	public SimpleCache() {
		this(10); 
	}

	/**
	 * A {@link SimpleCache} with room for 2^size fingerprints
	 * @param size Room for 2^size fps 
	 */
	public SimpleCache(final int size) {
		final int capacity = 1 << size;
		this.mask = capacity - 1;
		this.cache = new long[capacity];
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.Cache#hit(long)
	 */
	public boolean hit(final long fp) {
	    final int index = (int)(fp & this.mask);
	    long hit = this.cache[index];
	    if (hit == fp) {
	    	cacheHit++;
	    	return true;
	    } else {
	    	cacheMiss++;
	    	this.cache[index] = fp;
	    	return false;
	    }
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.Cache#getHitRatio()
	 */
	public double getHitRatio() {
		return cacheHit / (double) cacheMiss;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.Cache#getHitRatioAsString()
	 */
	public String getHitRatioAsString() {
		DecimalFormat df = new DecimalFormat("###,###.###");
		return df.format(getHitRatio());
	}

	/* (non-Javadoc)
	 * @see tlc2.util.Cache#getHitRate()
	 */
	public long getHitRate() {
		return cacheHit;
	}
}
