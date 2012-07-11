// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.fp;

public interface FPSetStatistic {

	/**
	 * @return the bucketsCapacity counting all allocated (used and unused) fp slots in the in-memory storage.
	 */
	public long getBucketCapacity();
	
	/**
	 * @return The allocated (used and unused) array length of the first level in-memory storage.
	 */
	public int getTblCapacity();

	/**
	 * @return the index.length
	 */
	public int getIndexCapacity();

	/**
	 * @return {@link DiskFPSet#getBucketCapacity()} + {@link DiskFPSet#getTblCapacity()} + {@link DiskFPSet#getIndexCapacity()}.
	 */
	public long getOverallCapacity();
	
	/**
	 * @return	Number of used slots in tbl by a bucket
	 * {@link DiskFPSet#getTblLoad()} <= {@link DiskFPSet#getTblCnt()}
	 */
	public int getTblLoad();
	
	/**
	 * @return the amount of fingerprints stored in memory. This is less or equal to {@link DiskFPSet#getTblCnt()} depending on if there collision buckets exist. 
	 */
	public int getTblCnt();
	
	/**
	 * @return the maximal amount of fingerprints stored in memory. 
	 */
	public int getMaxTblCnt();
	
	/**
	 * @return the amount of fingerprints stored on disk
	 */
	public long getFileCnt();
	
	/**
	 * @return the diskLookupCnt
	 */
	public long getDiskLookupCnt();

	/**
	 * @return the diskHitCnt
	 */
	public long getMemHitCnt();

	/**
	 * @return the diskHitCnt
	 */
	public long getDiskHitCnt();

	/**
	 * @return the diskWriteCnt
	 */
	public long getDiskWriteCnt();

	/**
	 * @return the diskSeekCnt
	 */
	public long getDiskSeekCnt();
	
	/**
	 * @return the growDiskMark
	 */
	public int getGrowDiskMark();
	
	/**
	 * @return the checkPointMark
	 */
	public int getCheckPointMark();
	
	public long sizeof();
}
