package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github1394gTest extends ModelCheckerTestCase {

	public Github1394gTest() {
		super("Github1394", new String[] { "-config", "Github1394g.cfg" }, EC.ExitStatus.ERROR_CONFIG_PARSE);
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
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CONFIG_THEOREM_NOT_CHECKABLE, "invariant", "Small"));
	}
}
