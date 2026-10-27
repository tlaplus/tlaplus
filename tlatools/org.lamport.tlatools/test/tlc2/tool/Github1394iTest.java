package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

// PROPERTY SpecTypeOK under INIT/NEXT: Spec is not the configured SPECIFICATION
public class Github1394iTest extends ModelCheckerTestCase {

	public Github1394iTest() {
		super("Github1394", new String[] { "-config", "Github1394i.cfg" }, EC.ExitStatus.ERROR);
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
