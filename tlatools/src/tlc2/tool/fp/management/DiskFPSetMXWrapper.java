// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp.management;

import javax.management.NotCompliantMBeanException;

import tlc2.tool.fp.FPSetStatistic;
import tlc2.tool.management.TLCStandardMBean;

//TODO dispose when underlying diskfpset is nulled (otherwise we end up holding a reference and diskfpset is never gced) 
public class DiskFPSetMXWrapper extends TLCStandardMBean implements DiskFPSetMXBean {

	private static int COUNT = 0;
	
	protected final FPSetStatistic fpset;

	private final String objectName;
	
	public DiskFPSetMXWrapper(final FPSetStatistic diskFPSet) throws NotCompliantMBeanException {
		super(DiskFPSetMXBean.class);
		fpset = diskFPSet;
		
		objectName = "DiskFPSet" + COUNT++;
		registerMBean("tlc2.tool.fp:type=" + objectName);
	}
	
	public String getObjectName() {
		return objectName;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getTblCnt()
	 */
	public long getTblCnt() {
		return fpset.getTblCnt();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getFileCnt()
	 */
	public long getFileCnt() {
		return fpset.getFileCnt();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getIndexCnt()
	 */
	public long getIndexCnt() {
		return fpset.getIndexCapacity();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getDiskLookupCnt()
	 */
	public long getDiskLookupCnt() {
		return fpset.getDiskLookupCnt();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getMemHitCnt()
	 */
	public long getMemHitCnt() {
		return fpset.getMemHitCnt();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getDiskHitCnt()
	 */
	public long getDiskHitCnt() {
		return fpset.getDiskHitCnt();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getDiskWriteCnt()
	 */
	public long getDiskWriteCnt() {
		return fpset.getDiskWriteCnt();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getDiskSeekCnt()
	 */
	public long getDiskSeekCnt() {
		return fpset.getDiskSeekCnt();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#getDiskSeekCache()
	 */
	public long getDiskSeekCache() {
		return fpset.getDiskSeekCache();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#getDiskSeekRate()
	 */
	public double getDiskSeekRate() {
		final long diskSeekCnt = getDiskSeekCnt();
		final long diskSeekCache = getDiskSeekCache();
		return diskSeekCache / (double) (diskSeekCache + diskSeekCnt);
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getCheckPointMark()
	 */
	public int getGrowDiskMark() {
		return fpset.getGrowDiskMark();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getCheckPointMark()
	 */
	public int getCheckPointMark() {
		return fpset.getCheckPointMark();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#getBucketCapacity()
	 */
	public long getBucketCapacity() {
		return fpset.getBucketCapacity();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#getTblCapacity()
	 */
	public long getTblCapacity() {
		return fpset.getTblCapacity();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#getOverallCapacity()
	 */
	public long getOverallCapacity() {
		return fpset.getOverallCapacity();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#getTblLoad()
	 */
	public long getTblLoad() {
		return fpset.getTblLoad();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#sizeof()
	 */
	public long getSizeOf() {
		return fpset.sizeof();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#getFlushTime()
	 */
	public long getFlushTime() {
		return fpset.getFlushTime();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#getReaderWriterCnt()
	 */
	public int getReaderWriterCnt() {
		return fpset.getReaderWriterCnt();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#getCollisionBucketCnt()
	 */
	public long getCollisionBucketCnt() {
		return fpset.getCollisionBucketCnt();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#getCollisionRatio()
	 */
	public double getCollisionRatio() {
		return fpset.getCollisionRatio();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#getLoadFactor()
	 */
	public double getLoadFactor() {
		return fpset.getLoadFactor();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetMXBean#forceFlush()
	 */
	public void forceFlush() {
		fpset.forceFlush();
	}
}
