// Copyright (c) 2022, Oracle and/or its affiliates.

package tlc2.tool.liveness;

import org.junit.Test;
import tlc2.output.EC;

import static org.junit.Assert.assertTrue;

public class Github702Test extends ModelCheckerTestCase {

	public Github702Test() {
		super("Github702", new String[] { "-config", "Github702.cfg" }, EC.ExitStatus.SUCCESS);
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_SUCCESS));
	}
}
