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

package tlc2.util.statistics;

/**
 * Doesn't really do a thing. Can be instantiated multiple times contrary to
 * BucketStatistics which registers itself via JMX.
 */
public class DummyBucketStatistics implements IBucketStatistics {

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.IBucketStatistics#addSample(int)
	 */
	public void addSample(int amount) {
		// ignore
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.IBucketStatistics#getObservations()
	 */
	public long getObservations() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.IBucketStatistics#getMedian()
	 */
	public int getMedian() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.IBucketStatistics#getMean()
	 */
	public double getMean() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.IBucketStatistics#getMin()
	 */
	public int getMin() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.IBucketStatistics#getMax()
	 */
	public int getMax() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.IBucketStatistics#getStdDev()
	 */
	public double getStdDev() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see tlc2.util.statistics.IBucketStatistics#getPercentile(double)
	 */
	public double getPercentile(double quantile) {
		return 0;
	}
}
