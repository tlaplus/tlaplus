// Copyright (c) 2023, Oracle and/or its affiliates.

package tlc2.tool;

import static org.junit.Assert.assertTrue;

import java.io.IOException;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github817Test extends ModelCheckerTestCase {

	public Github817Test() {
		super("Github817", new String[] { "-config", "Github817.tla" }, EC.ExitStatus.SUCCESS);
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Test
	public void testSpec() throws IOException {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recorded(EC.TLC_SUCCESS));
	}

}
