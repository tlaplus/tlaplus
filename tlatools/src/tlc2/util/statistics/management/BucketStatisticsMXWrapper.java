/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package tlc2.util.statistics.management;

import javax.management.NotCompliantMBeanException;

import tlc2.tool.management.TLCStandardMBean;
import tlc2.util.statistics.IBucketStatistics;

public class BucketStatisticsMXWrapper extends TLCStandardMBean implements BucketStatisticsMXBean {

	private IBucketStatistics graphStats;

	private final String objectName;

	public BucketStatisticsMXWrapper(final IBucketStatistics graphStats, final String graphName, final String pkg)
			throws NotCompliantMBeanException {
		super(BucketStatisticsMXBean.class);
		this.graphStats = graphStats;
		
		objectName = graphName;
		registerMBean(String.format("%s:type=%s", pkg, objectName));
	}
	
	/* (non-Javadoc)
	 * @see tlc2.util.statistics.management.GraphStatisticsMXBean#getObjectName()
	 */
	public String getObjectName() {
		return objectName;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.management.GraphStatisticsMXBean#getObservations()
	 */
	public long getObservations() {
		return graphStats.getObservations();
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.management.GraphStatisticsMXBean#getMedian()
	 */
	public int getMedian() {
		return graphStats.getMedian();
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.management.GraphStatisticsMXBean#getMean()
	 */
	public double getMean() {
		return graphStats.getMean();
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.management.GraphStatisticsMXBean#getMin()
	 */
	public int getMin() {
		return graphStats.getMin();
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.management.GraphStatisticsMXBean#getMax()
	 */
	public int getMax() {
		return graphStats.getMax();
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.management.GraphStatisticsMXBean#getStdDev()
	 */
	public double getStdDev() {
		return graphStats.getStdDev();
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.management.GraphStatisticsMXBean#get75Percentile()
	 */
	public double get75Percentile() {
		return graphStats.getPercentile(0.75d);
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.management.GraphStatisticsMXBean#get95Percentile()
	 */
	public double get95Percentile() {
		return graphStats.getPercentile(0.95d);
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.management.GraphStatisticsMXBean#get98Percentile()
	 */
	public double get98Percentile() {
		return graphStats.getPercentile(0.98d);
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.management.GraphStatisticsMXBean#get99Percentile()
	 */
	public double get99Percentile() {
		return graphStats.getPercentile(0.99d);
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.management.GraphStatisticsMXBean#get999Percentile()
	 */
	public double get999Percentile() {
		return graphStats.getPercentile(0.999d);
	}
}
