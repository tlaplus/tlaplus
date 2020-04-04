// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp.management;

import java.io.IOException;

import tlc2.tool.fp.DiskFPSet;
import tlc2.tool.fp.FPSet;

public interface DiskFPSetMXBean {

	/**
	 * @return The version of TLC.
	 */
	String getVersion();
	
	/**
	 * @return The code revision corresponding to this version of TLC.
	 */
	String getRevision();
	
	/**
	 * @see DiskFPSet#getDiskHitCnt()
	 */
	long getDiskHitCnt();
	/**
	 * @see DiskFPSet#getDiskLookupCnt()
	 */
	long getDiskLookupCnt();
	/**
	 * @see DiskFPSet#getDiskSeekCnt()
	 */
	long getDiskSeekCnt();
	/**
	 * @see DiskFPSet#getDiskSeekCache()
	 */
	long getDiskSeekCache();
	/**
	 * @see DiskFPSet#getDiskSeekRate()
	 */
	double getDiskSeekRate();
	/**
	 *@see DiskFPSet#getDiskWriteCnt()
	 */
	long getDiskWriteCnt();

	/**
	 * @see DiskFPSet#getMemHitCnt()
	 */
	long getMemHitCnt();

	/**
	 * @see DiskFPSet#getFileCnt()
	 */
	long getFileCnt();
	/**
	 * @see DiskFPSet#getIndexCapacity()
	 */
	long getIndexCnt();

	/**
	 * ~ getMemWriteCnt()
	 */
	long getTblCnt();
	
	/**
	 * @see DiskFPSet#getBucketCapacity()
	 */
	long getBucketCapacity();
	/**
	 * @see DiskFPSet#getTblCapacity()
	 */
	long getTblCapacity();
	/**
	 * @see DiskFPSet#getOverallCapacity()
	 */
	long getOverallCapacity();

	/**
	 * @see DiskFPSet#getTblLoad()
	 */
	long getTblLoad();
	
	/**
	 * @see DiskFPSet#getGrowDiskMark()
	 */
	int getGrowDiskMark();
	/**
	 * @see DiskFPSet#getCheckPointMark()
	 */
	int getCheckPointMark();
	
	/**
	 * @return
	 */
	long getSizeOf();
	
	/**
	 * @return Accumulated time it has taken to flush {@link FPSet} to disk
	 */
	long getFlushTime();
	
	/**
	 * @see DiskFPSet#getLockCnt()
	 */
	int getLockCnt();
	
	/**
	 * @see DiskFPSet#getReaderWriterCnt()
	 */
	int getReaderWriterCnt();
	
	/**
	 * @see DiskFPSet#getLoadFactor()
	 */
	double getLoadFactor();
	
	/**
	 * @see DiskFPSet#forceFlush()
	 */
	void forceFlush();
	
	/**
	 * @see DiskFPSet#checkInvariant()
	 */
	boolean checkInvariant() throws IOException;
}
