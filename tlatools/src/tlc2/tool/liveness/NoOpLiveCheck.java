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

import java.io.IOException;

import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.LongVec;
import tlc2.util.statistics.DummyBucketStatistics;
import tlc2.util.statistics.IBucketStatistics;

public class NoOpLiveCheck implements ILiveCheck {

	private final Tool tool;
	private final String metadir;
	private final IBucketStatistics stats;

	public NoOpLiveCheck(Tool tool, String metadir) {
		this.tool = tool;
		this.metadir = metadir;
		this.stats = new DummyBucketStatistics();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#addInitState(tlc2.tool.TLCState, long)
	 */
	public void addInitState(TLCState state, long stateFP) {
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#addNextState(tlc2.tool.TLCState, long, tlc2.tool.StateVec, tlc2.util.LongVec)
	 */
	public void addNextState(TLCState s0, long fp0, StateVec nextStates, LongVec nextFPs) throws IOException {
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#doLiveCheck()
	 */
	public boolean doLiveCheck() {
		return false;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#check(boolean)
	 */
	public boolean check(boolean forceCheck) throws Exception {
		return true;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#finalCheck()
	 */
	public boolean finalCheck() throws Exception {
		return true;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#checkTrace(tlc2.tool.StateVec)
	 */
	public void checkTrace(StateVec trace) throws IOException, InterruptedException {
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#getMetaDir()
	 */
	public String getMetaDir() {
		return metadir;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#getTool()
	 */
	public Tool getTool() {
		return tool;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#getOutDegreeStatistics()
	 */
	public IBucketStatistics getOutDegreeStatistics() {
		return null;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#getChecker(int)
	 */
	public ILiveChecker getChecker(int idx) {
		return null;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#getNumChecker()
	 */
	public int getNumChecker() {
		return 0;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#close()
	 */
	public void close() throws IOException {
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#beginChkpt()
	 */
	public void beginChkpt() throws IOException {
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#commitChkpt()
	 */
	public void commitChkpt() throws IOException {
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#recover()
	 */
	public void recover() throws IOException {
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#calculateInDegreeDiskGraphs(tlc2.util.statistics.IBucketStatistics)
	 */
	public IBucketStatistics calculateInDegreeDiskGraphs(IBucketStatistics aGraphStats) throws IOException {
		return stats;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#calculateOutDegreeDiskGraphs(tlc2.util.statistics.IBucketStatistics)
	 */
	public IBucketStatistics calculateOutDegreeDiskGraphs(IBucketStatistics aGraphStats) throws IOException {
		return stats;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.ILiveCheck#reset()
	 */
	public void reset() throws IOException {
	}
}
