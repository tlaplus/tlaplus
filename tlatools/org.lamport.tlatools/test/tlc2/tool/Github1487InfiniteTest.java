/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Ignore;
import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;
import tlc2.tool.queue.DiskStateQueue;

/**
 * https://github.com/tlaplus/tlaplus/issues/1487: With a VIEW that does not
 * contain them, TLC never fingerprints the infinite values Nat, SUBSET Nat,
 * [n \in Nat |-> n], and {n \in Nat : n > 0}, and explores their states as long
 * as the states stay in memory. The result must not depend on whether the
 * DiskStateQueue swaps the states out to disk, which fails with "Can not pickle
 * the value" or a NullPointerException, upon which StatePoolWriter exits TLC.
 *
 * @see Github1487Test
 */
@Ignore("https://github.com/tlaplus/tlaplus/issues/1487")
public class Github1487InfiniteTest extends ModelCheckerTestCase {

	public Github1487InfiniteTest() {
		super("Github1487Infinite");
	}

	@Override
	protected void beforeSetUp() {
		// Spill every state to disk. Read once, when DiskStateQueue is initialized.
		System.setProperty(DiskStateQueue.class.getName() + ".BufSize", "1");
	}

	@Override
	protected int getNumberOfThreads() {
		return 4;
	}

	@Override
	protected boolean doCoverage() {
		// Coverage fails for infinite values.
		return false;
	}

	@Override
	protected boolean doDump() {
		// Printing the states to the dot file would enumerate the infinite values.
		return false;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Test
	public void testSpec() {
		assertFalse(recorder.recorded(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR));
		assertFalse(recorder.recorded(EC.SYSTEM_ERROR_WRITING_STATES));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		// 64 initial states, each with a chain of 3 successors.
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "256", "256", "0"));
	}
}
