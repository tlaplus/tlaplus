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
package tlc2.tool.queue;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Ignore;
import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * The result of model checking must not depend on whether the
 * {@link DiskStateQueue} swapped states out to disk. A non-ASCII string read
 * back from disk keeps its token but not its text, so ToString(s) differs from
 * ToString of the literal, and TLC reports a bogus invariant violation. (The
 * state counts are unaffected, because the fingerprint of a string also only
 * looks at the low byte of each char.)
 * 
 * @see <a href="https://github.com/tlaplus/tlaplus/issues/1076">#1076</a>
 */
@Ignore("https://github.com/tlaplus/tlaplus/issues/1076")
public class UnicodeStringDiskStateQueueTest extends ModelCheckerTestCase {

	public UnicodeStringDiskStateQueueTest() {
		super("UnicodeStringDiskStateQueue");
	}

	@Override
	protected void beforeSetUp() {
		// Spill every state to disk. Read once, when DiskStateQueue is initialized.
		System.setProperty(DiskStateQueue.class.getName() + ".BufSize", "1");
	}

	@Test
	public void testSpec() {
		assertFalse(recorder.recorded(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR));
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		// Two strings times i \in 0..10.
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "22", "22", "0"));
	}
}
