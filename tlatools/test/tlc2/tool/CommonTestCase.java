/*******************************************************************************
 * Copyright (c) 2016 Microsoft Research. All rights reserved. 
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

package tlc2.tool;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertTrue;

import java.io.File;
import java.util.List;

import tlc2.TLCGlobals;
import tlc2.TestMPRecorder;
import tlc2.output.EC;
import tlc2.output.MPRecorder;
import tlc2.tool.liveness.GraphNode;
import tlc2.util.BitVector;
import tlc2.util.BufferedRandomAccessFile;

public abstract class CommonTestCase {

	protected static final String BASE_DIR = System.getProperty("basedir", "");
	protected static final String TEST_MODEL = "test-model" + File.separator;
	protected static final String BASE_PATH = BASE_DIR + TEST_MODEL;

	protected final TestMPRecorder recorder;

	public CommonTestCase(TestMPRecorder testMPRecorder) {
		recorder = testMPRecorder;
	}

	/**
	 * Asserts that the actual trace and the expected error trace are equal.
	 * 
	 * @param actual
	 *            The actual trace as recorded by {@link MPRecorder}.
	 * @param expectedTrace
	 *            The expected trace.
	 */
	protected void assertTraceWith(final List<Object> actual, final List<String> expectedTrace) {
		assertEquals(expectedTrace.size(), actual.size());
		for (int i = 0; i < expectedTrace.size(); i++) {
			final Object[] objs = (Object[]) actual.get(i);
			final TLCStateInfo stateInfo = (TLCStateInfo) objs[0];
			final String info = (String) stateInfo.info;
			if (i == 0) {
				// The first state has to be an initial state.
				"<Initial predicate>".equals(info);
			} else {
				// ... all others are reachable via an action.
				info.startsWith("<Action");
			}
			assertEquals(expectedTrace.get(i), 
					   stateInfo.toString().trim()); // trimmed to remove any newlines or whitespace
			assertEquals(i+1, objs[1]);
		}
	}

	/**
	 * Asserts that the error trace ends in stuttering at the given number.
	 * 
	 * @param stateNum
	 *            The number of the stuttering state
	 */
	protected void assertStuttering(int stateNum) {
		assertTrue(recorder.recorded(EC.TLC_STATE_PRINT3));
		List<Object> stutter = recorder.getRecords(EC.TLC_STATE_PRINT3);
		assertTrue(stutter.size() > 0);
		Object[] object = (Object[]) stutter.get(0);
		assertEquals(stateNum, object[1]);
	}

	/**
	 * Asserts that the error trace loops back to the state with the given
	 * number.
	 * 
	 * @param i The loop back state number.
	 */
	protected void assertBackToState(int stateNum) {
		assertTrue(recorder.recorded(EC.TLC_BACK_TO_STATE));
		List<Object> loop = recorder.getRecords(EC.TLC_BACK_TO_STATE);
		assertTrue(loop.size() > 0);
		Object[] object = (Object[]) loop.get(0);
		assertEquals(Integer.toString(stateNum), object[0]);
	}

	/**
	 * Asserts that the error trace loops back to the state with the given
	 * number.
	 * 
	 * @param i The loop back state number.
	 * @param action The action label associated with the loop back marker
	 */
	protected void assertBackToState(int stateNum, final String action) {
		assertTrue(recorder.recorded(EC.TLC_BACK_TO_STATE));
		List<Object> loop = recorder.getRecords(EC.TLC_BACK_TO_STATE);
		assertTrue(loop.size() > 0);
		Object[] object = (Object[]) loop.get(0);
		assertTrue(object.length > 1);
		assertEquals(Integer.toString(stateNum), object[0]);
		assertEquals(action, object[1]);
	}

	/**
	 * Check the file size of the AbstractDiskGraph files to assert that the
	 * expected amount of ptrs and nodes (outgoing arcs) have been written to
	 * disk.
	 * <p>
	 * CAUTION: The order in which the transitions are inserted into the
	 * {@link GraphNode} determines the size of the {@link BitVector}. I.e. if
	 * the truth values of the first N nodes inserted are true, and the
	 * remainder is false, the BitVector's size will correspond to N. However,
	 * if the first N truth values are false, followed by M trues, the
	 * BitVector's size is N + M.
	 * <p>
	 * See {@link GraphNode}'s constructor: it initializes {@link BitVector}
	 * with capacity zero and subsequently grows BV when bits are set to true.
	 * <p>
	 * 
	 * @see BitVector#read(BufferedRandomAccessFile)
	 * @see BitVector#write(BufferedRandomAccessFile)
	 * @see GraphNode#read(BufferedRandomAccessFile)
	 * @see GraphNode#write(BufferedRandomAccessFile)
	 * 
	 * @param nodesSize
	 * @param ptrsSize
	 */
	protected void assertNodeAndPtrSizes(final long nodesSize, final long ptrsSize) {
		final String metadir = TLCGlobals.mainChecker.metadir;
		assertNotNull(metadir);
		
		final File nodes = new File(metadir + File.separator + "nodes_0");
		assertTrue(nodes.exists());
		assertEquals(nodesSize, nodes.length());
	
		final File ptrs =  new File(metadir + File.separator + "ptrs_0");
		assertTrue(ptrs.exists());
		assertEquals(ptrsSize, ptrs.length());
	}

}
