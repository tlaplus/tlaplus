/*******************************************************************************
 * Copyright (c) 2026 Oracle and/or its affiliates. All rights reserved.
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
 ******************************************************************************/
package tlc2.tool.liveness;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;

/**
 * Reproduces https://github.com/tlaplus/tlaplus/issues/1523.
 */
public class Github1523Test extends ModelCheckerTestCase {

	public Github1523Test() {
		// The 96-state SCC fills the initial table to its resize threshold.
		// With polynomial 7, resizing during the scan moves the accepting row past the scan limit.
		super("SccResizeLiveness", new String[] { "-seed", "1", "-fp", "7" }, ExitStatus.VIOLATION_LIVENESS);
	}

	@Override
	protected boolean noRandomFPandSeed() {
		return false;
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
	public void testFairCycleViolatesProperty() {
		assertTrue("Expected TLC to explore all 96 distinct states",
				recorder.recordedWithStringValues(EC.TLC_STATS, "97", "96"));
		assertTrue("The fair cycle visits x = 0 infinitely often",
				recorder.recordedWithStringValue(EC.TLC_TEMPORAL_PROPERTY_VIOLATED, "Property"));
	}
}
