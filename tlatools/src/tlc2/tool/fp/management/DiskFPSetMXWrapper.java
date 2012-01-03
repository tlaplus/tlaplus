// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp.management;

import java.lang.management.ManagementFactory;

import javax.management.InstanceAlreadyExistsException;
import javax.management.MBeanRegistrationException;
import javax.management.MBeanServer;
import javax.management.MalformedObjectNameException;
import javax.management.NotCompliantMBeanException;
import javax.management.ObjectName;
import javax.management.StandardMBean;

import tlc2.tool.fp.DiskFPSet;

public class DiskFPSetMXWrapper extends StandardMBean implements DiskFPSetMXBean {

	private static int COUNT = 0;
	
	private final DiskFPSet fpset;
	
	public DiskFPSetMXWrapper(final DiskFPSet diskFPSet) throws NotCompliantMBeanException {
		super(DiskFPSetMXBean.class);
		fpset = diskFPSet;
		
		// register monitoring mx bean
		MBeanServer mbs = ManagementFactory.getPlatformMBeanServer(); 
        ObjectName mxbeanName;
		try {
			mxbeanName = new ObjectName("tlc2.tool.fp:type=DiskFPSet" + COUNT++);
			mbs.registerMBean(this, mxbeanName);
		} catch (MalformedObjectNameException e1) {
			e1.printStackTrace();
		} catch (NullPointerException e1) {
			e1.printStackTrace();
		} catch (InstanceAlreadyExistsException e) {
			e.printStackTrace();
		} catch (MBeanRegistrationException e) {
			e.printStackTrace();
		} catch (NotCompliantMBeanException e) {
			e.printStackTrace();
		}
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
		return fpset.getIndexCnt();
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
}
