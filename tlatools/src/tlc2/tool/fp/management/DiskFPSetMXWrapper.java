// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp.management;

import javax.management.NotCompliantMBeanException;

import tlc2.tool.fp.FPSetStatistic;
import tlc2.tool.management.TLCStandardMBean;

//TODO dispose when underlying diskfpset is nulled (otherwise we end up holding a reference and diskfpset is never gced) 
public class DiskFPSetMXWrapper extends TLCStandardMBean implements DiskFPSetMXBean {

	private static int COUNT = 0;
	
	protected final FPSetStatistic fpset;
	
	public DiskFPSetMXWrapper(final FPSetStatistic diskFPSet) throws NotCompliantMBeanException {
		super(DiskFPSetMXBean.class);
		fpset = diskFPSet;
		
		registerMBean("tlc2.tool.fp:type=DiskFPSet" + COUNT++);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getTblCnt()
	 */
	public int getTblCnt() {
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
	public int getIndexCnt() {
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
	public int getTblCapacity() {
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
	public int getTblLoad() {
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
}
