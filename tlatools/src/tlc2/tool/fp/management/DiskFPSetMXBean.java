// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp.management;

import tlc2.tool.fp.DiskFPSet;

public interface DiskFPSetMXBean {

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
	int getIndexCnt();

	/**
	 * ~ getMemWriteCnt()
	 */
	int getTblCnt();
	
	/**
	 * @see DiskFPSet#getBucketCapacity()
	 */
	public long getBucketCapacity();
	/**
	 * @see DiskFPSet#getTblCapacity()
	 */
	public int getTblCapacity();
	/**
	 * @see DiskFPSet#getOverallCapacity()
	 */
	public long getOverallCapacity();

	/**
	 * @see DiskFPSet#getTblLoad()
	 */
	public int getTblLoad();
	
	/**
	 * @see DiskFPSet#getGrowDiskMark()
	 */
	int getGrowDiskMark();
	/**
	 * @see DiskFPSet#getCheckPointMark()
	 */
	int getCheckPointMark();
}
