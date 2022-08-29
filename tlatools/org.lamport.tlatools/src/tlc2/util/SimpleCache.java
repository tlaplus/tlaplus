// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.util;

import java.text.DecimalFormat;

public class SimpleCache implements Cache {

    private final long mask;
    private final long[] cache;
    private volatile long cacheHit = 1L;
    private volatile long cacheMiss = 1L;

    /**
     * A {@link SimpleCache} with room for 2^10 (1024) fingerprints
     */
    public SimpleCache() {
        this(10);
    }

    /**
     * A {@link SimpleCache} with room for 2^size fingerprints
     *
     * @param size Room for 2^size fps
     */
    public SimpleCache(final int size) {
        final int capacity = 1 << size;
        this.mask = capacity - 1L;
        this.cache = new long[capacity];
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.Cache#hit(long)
     */
    @Override
    public boolean hit(final long fp) {
        final int index = (int) (fp & this.mask);
        final long hit = this.cache[index];
        if (hit == fp) {
            long newValue = cacheHit + 1;
            cacheHit = newValue;
            return true;
        } else {
            long newValue = cacheMiss + 1;
            cacheMiss = newValue;
            this.cache[index] = fp;
            return false;
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.Cache#getHitRatio()
     */
    @Override
    public double getHitRatio() {
        return cacheHit / (double) cacheMiss;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.Cache#getHitRatioAsString()
     */
    @Override
    public String getHitRatioAsString() {
        final DecimalFormat df = new DecimalFormat("###,###.###");
        return df.format(getHitRatio());
    }

    /* (non-Javadoc)
     * @see tlc2.util.Cache#getHitRate()
     */
    @Override
    public long getHitRate() {
        return cacheHit;
    }
}
