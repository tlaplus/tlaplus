// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.util;

public interface Cache {
	/**
	 * Tests if the given fingerprint is in this cache, adding it as a side
	 * effect if not.
	 * 
	 * @param fingerprint
	 *            fingerprint to be tested
	 * @return true iff given fingerprint is in cache
	 */
	boolean hit(long fingerprint);
	/**
	 * @return Ratio of cache hits and misses
	 */
	double getHitRatio();
	/**
	 * @return A pretty printed version of {@link Cache#getHitRatio()}
	 */
	String getHitRatioAsString();
	/**
	 * @return Absolute value for cache hits
	 */
	long getHitRate();
}
