// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp.management;

public interface DiskFPSetMXBean {

	long getDiskHitCnt();
	long getDiskLookupCnt();
	long getDiskSeekCnt();
	long getDiskWriteCnt();

	long getMemHitCnt();

	long getFileCnt();
	int getIndexCnt();

	/**
	 * ~ getMemWriteCnt()
	 */
	int getTblCnt();
	
	int getGrowDiskMark();
	int getCheckPointMark();
}
