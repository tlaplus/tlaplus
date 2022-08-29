// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.IOException;

public interface FPSetStatistic {

    /**
     * @return the bucketsCapacity counting all allocated (used and unused) fp slots in the in-memory storage.
     */
    long getBucketCapacity();

    /**
     * @return The allocated (used and unused) array length of the first level in-memory storage.
     */
    long getTblCapacity();

    /**
     * @return the index.length
     */
    long getIndexCapacity();

    /**
     * @return {@link DiskFPSet#getBucketCapacity()} + {@link DiskFPSet#getTblCapacity()} + {@link DiskFPSet#getIndexCapacity()}.
     */
    long getOverallCapacity();

    /**
     * @return Number of used slots in tbl by a bucket
     * {@link DiskFPSet#getTblLoad()} <= {@link DiskFPSet#getTblCnt()}
     */
    long getTblLoad();

    /**
     * @return the amount of fingerprints stored in memory. This is less or equal to {@link DiskFPSet#getTblCnt()} depending on if there collision buckets exist.
     */
    long getTblCnt();

    /**
     * @return the maximal amount of fingerprints stored in memory.
     */
    long getMaxTblCnt();

    /**
     * @return the amount of fingerprints stored on disk
     */
    long getFileCnt();

    /**
     * @return the diskLookupCnt
     */
    long getDiskLookupCnt();

    /**
     * @return the diskHitCnt
     */
    long getMemHitCnt();

    /**
     * @return the diskHitCnt
     */
    long getDiskHitCnt();

    /**
     * @return the diskWriteCnt
     */
    long getDiskWriteCnt();

    /**
     * @return the diskSeekCnt
     */
    long getDiskSeekCnt();

    /**
     * @return the diskSeekCache
     */
    long getDiskSeekCache();

    /**
     * @return the growDiskMark
     */
    int getGrowDiskMark();

    /**
     * @return the checkPointMark
     */
    int getCheckPointMark();

    /**
     * @return The memory size of the {@link DiskFPSet}
     */
    long sizeof();

    /**
     * @return Accumulated time it has taken to flush {@link FPSet} to disk
     */
    long getFlushTime();

    /**
     * @return DiskFPSet#getLockCnt()
     */
    int getLockCnt();

    /**
     * @see DiskFPSet#getReaderWriterCnt()
     */
    int getReaderWriterCnt();

    /**
     * @return DiskFPSet#getLoadFactor();
     */
    double getLoadFactor();

    /**
     *
     */
    void forceFlush();

    /**
     * @see DiskFPSet#checkInvariant()
     */
    boolean checkInvariant() throws IOException;
}
