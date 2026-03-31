/*******************************************************************************
 * Copyright (c) 2026 Contributors. All rights reserved.
 *
 * The MIT License (MIT)
 ******************************************************************************/
package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.TestPrintStream;
import util.ToolIO;

public class RandomConstantOverrideTest extends ModelCheckerTestCase {

	private TestPrintStream testPrintStream;

	public RandomConstantOverrideTest() {
		super("RandomConstantOverride");
	}

	@Override
	protected void beforeSetUp() {
		testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
	}

	@Override
	protected boolean runWithDebugger() {
		return false;
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recorded(EC.TLC_SUCCESS));
		assertTrue(testPrintStream.countSubstring("RAND_EVAL") > 1);
	}
}
