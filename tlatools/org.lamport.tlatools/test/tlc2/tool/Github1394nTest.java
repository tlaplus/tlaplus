package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

// PROPERTY A!SpecSmall where A substitutes x + 1 for x: A!Spec is not the configured SPECIFICATION
public class Github1394nTest extends ModelCheckerTestCase {

	public Github1394nTest() {
		super("Github1394Ext", new String[] { "-config", "Github1394n.cfg" }, EC.ExitStatus.ERROR);
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
		assertTrue(recorder.recorded(EC.TLC_LIVE_WRONG_FORMULA_FORMAT));
	}
}
