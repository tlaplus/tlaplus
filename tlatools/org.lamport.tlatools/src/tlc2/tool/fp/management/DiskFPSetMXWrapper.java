// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp.management;

import tlc2.tool.fp.FPSetStatistic;
import tlc2.tool.management.TLCStandardMBean;

import javax.management.NotCompliantMBeanException;
import java.io.IOException;

//TODO dispose when underlying diskfpset is nulled (otherwise we end up holding a reference and diskfpset is never gced) 
public class DiskFPSetMXWrapper extends TLCStandardMBean implements DiskFPSetMXBean {

    private static int COUNT = 0;

    protected final FPSetStatistic fpset;

    private final String objectName;

    public DiskFPSetMXWrapper(final FPSetStatistic diskFPSet) throws NotCompliantMBeanException {
        super(DiskFPSetMXBean.class);
        fpset = diskFPSet;

        // Append ",name=COUNT" suffix to objectname to expose all DiskFPSet instances
        // as children of type DiskFPSet. However, jfr2jmx does not support it, nor does
        // jmx2munin used by cloud based distributed TLC.
        objectName = "DiskFPSet" + COUNT++;
        registerMBean("tlc2.tool.fp:type=" + objectName/* + ",name=" + COUNT++*/);
    }

    public String getObjectName() {
        return objectName;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getTblCnt()
     */
    @Override
    public long getTblCnt() {
        return fpset.getTblCnt();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getFileCnt()
     */
    @Override
    public long getFileCnt() {
        return fpset.getFileCnt();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getIndexCnt()
     */
    @Override
    public long getIndexCnt() {
        return fpset.getIndexCapacity();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getDiskLookupCnt()
     */
    @Override
    public long getDiskLookupCnt() {
        return fpset.getDiskLookupCnt();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getMemHitCnt()
     */
    @Override
    public long getMemHitCnt() {
        return fpset.getMemHitCnt();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getDiskHitCnt()
     */
    @Override
    public long getDiskHitCnt() {
        return fpset.getDiskHitCnt();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getDiskWriteCnt()
     */
    @Override
    public long getDiskWriteCnt() {
        return fpset.getDiskWriteCnt();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getDiskSeekCnt()
     */
    @Override
    public long getDiskSeekCnt() {
        return fpset.getDiskSeekCnt();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#getDiskSeekCache()
     */
    @Override
    public long getDiskSeekCache() {
        return fpset.getDiskSeekCache();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#getDiskSeekRate()
     */
    @Override
    public double getDiskSeekRate() {
        final long diskSeekCnt = getDiskSeekCnt();
        final long diskSeekCache = getDiskSeekCache();
        return diskSeekCache / (double) (diskSeekCache + diskSeekCnt);
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getCheckPointMark()
     */
    @Override
    public int getGrowDiskMark() {
        return fpset.getGrowDiskMark();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetSamplerMXBean#getCheckPointMark()
     */
    @Override
    public int getCheckPointMark() {
        return fpset.getCheckPointMark();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#getBucketCapacity()
     */
    @Override
    public long getBucketCapacity() {
        return fpset.getBucketCapacity();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#getTblCapacity()
     */
    @Override
    public long getTblCapacity() {
        return fpset.getTblCapacity();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#getOverallCapacity()
     */
    @Override
    public long getOverallCapacity() {
        return fpset.getOverallCapacity();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#getTblLoad()
     */
    @Override
    public long getTblLoad() {
        return fpset.getTblLoad();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#sizeof()
     */
    @Override
    public long getSizeOf() {
        return fpset.sizeof();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#getFlushTime()
     */
    @Override
    public long getFlushTime() {
        return fpset.getFlushTime();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#getReaderWriterCnt()
     */
    @Override
    public int getReaderWriterCnt() {
        return fpset.getReaderWriterCnt();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#getLoadFactor()
     */
    @Override
    public double getLoadFactor() {
        return fpset.getLoadFactor();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#forceFlush()
     */
    @Override
    public void forceFlush() {
        fpset.forceFlush();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#checkInvariant()
     */
    @Override
    public boolean checkInvariant() throws IOException {
        return fpset.checkInvariant();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.fp.management.DiskFPSetMXBean#getLockCnt()
     */
    @Override
    public int getLockCnt() {
        return fpset.getLockCnt();
    }
}
