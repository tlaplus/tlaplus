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

package tlc2.tool.liveness;

import java.util.concurrent.atomic.AtomicInteger;

public class GraphStats {
	
	private static final int MAX = 32;
	
	/**
	 * nodesIn/OutDegree are two statistics of the distribution of links in the
	 * behavior graph.
	 * <p>
	 * Technically it uses AtomicLong to prevent threading issues. The array
	 * position is equivalent to the number of in/out links of a node. The last
	 * position is used as an overflow for when nodes have more than
	 * {@link GraphStats#maximum} links. Today's assumption is that there won't
	 * be many nodes with more than {@link GraphStats#MAX} links.
	 */
	private final AtomicInteger[] nodesDegree;
	
	/**
	 * Expected maximum number of edges.  
	 */
	private final int maximum;

	private final Direction direction;
	
	public enum Direction {IN, OUT};
	
	public GraphStats(Direction aDirection) {
		this(MAX, aDirection);
	}
	
	public GraphStats(int aMaximum, Direction aDirection) {
		this.maximum = aMaximum;
		this.direction = aDirection;
		nodesDegree = new AtomicInteger[this.maximum];
		for (int i = 0; i < nodesDegree.length; i++) {
			nodesDegree[i] = new AtomicInteger(0);
		}
	}

	public void addNodeEdgeCount(int edgeCount) {
		if (edgeCount < this.maximum - 1) {
			nodesDegree[edgeCount].getAndIncrement();
		} else {
			// Nodes with more than (maximum - 2) edges all
			// go into the last bucket. (0 bucket is for zero edges)
			nodesDegree[this.maximum - 1].getAndIncrement();
		}
	}

	public String toString() {
		final StringBuffer buf = new StringBuffer();
		buf.append("==============================\n");
		buf.append("=Historgram vertex " + direction + " degree=\n");
		buf.append("==============================\n");
		buf.append("numEdges/occurrences (log scale)\n");
		for (int i = 0; i < nodesDegree.length; i++) {
			int amount = nodesDegree[i].get();
			buf.append(String.format("%02d", i));
			buf.append(":");
			buf.append(String.format("%02d", amount));
			buf.append(" ");
			for (int j = 0; j < Math.log(amount); j++) {
				buf.append("#");
			}
			buf.append("\n");
		}
		buf.append("==============================");
		return buf.toString();
	}
}
