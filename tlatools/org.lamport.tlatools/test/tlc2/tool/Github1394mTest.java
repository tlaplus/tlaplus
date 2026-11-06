package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github1394mTest extends ModelCheckerTestCase {

	public Github1394mTest() {
		super("Github1394Ext", new String[] { "-config", "Github1394m.cfg" }, EC.ExitStatus.ERROR_CONFIG_PARSE);
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
		assertTrue(recorder.recordedWithStringValues(EC.TLC_CONFIG_THEOREM_NOT_CHECKABLE, "property", "A!SpecSmall"));
	}
}
