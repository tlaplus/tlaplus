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
package tlc2.tool.liveness;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;

public class Github763Test extends ModelCheckerTestCase {

	public Github763Test() {
		super("Github763", new String[] { "-config", "Github763.tla" }, EC.ExitStatus.ERROR);
	}

	@Override
	protected boolean runWithDebugger() {
		return false;
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}

	@Override
	protected boolean doDump() {
		return false;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));

		// Assert the error trace is printed.
		assertFalse(recorder.getRecords(EC.TLC_STATE_PRINT2).isEmpty());

		// Assert the error message is printed (regression: was previously missing).
		assertTrue(recorder.recordedWithStringValues(EC.GENERAL,
				"TLC threw an unexpected exception.\n" + "This was probably caused by an error in the spec or model.\n"
						+ "See the User Output or TLC Console for clues to what happened.\n"
						+ "The exception was a java.lang.RuntimeException\n"
						+ ": Attempted to check equality of the set {} with the value:\n" + "[val |-> 1]"));

		// Assert the nested expression (call stack) is printed.
		assertTrue(recorder.recorded(EC.TLC_NESTED_EXPRESSION));
	}
}
