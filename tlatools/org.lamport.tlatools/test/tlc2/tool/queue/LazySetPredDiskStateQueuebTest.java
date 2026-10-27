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

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Like {@link LazySetPredDiskStateQueueTest}, but the wrong value of v, which
 * SetPredValue#write wrote to disk, satisfies the invariant Violated, which the
 * filtered set violates. TLC thus missed the violation.
 *
 * @see <a href="https://github.com/tlaplus/tlaplus/issues/1445">#1445</a>
 */
public class LazySetPredDiskStateQueuebTest extends ModelCheckerTestCase {

	public LazySetPredDiskStateQueuebTest() {
		super("LazySetPredDiskStateQueue", new String[] { "-config", "LazySetPredDiskStateQueueb.cfg" },
				ExitStatus.VIOLATION_SAFETY);
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
	protected boolean doDump() {
		// Printing the states to the dot file would convert v.
		return false;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, "Violated"));
		assertFalse(recorder.recorded(EC.SYSTEM_ERROR_WRITING_STATES));
		assertFalse(recorder.recorded(EC.GENERAL));
	}
}
