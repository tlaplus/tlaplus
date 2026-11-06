package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github1394kTest extends ModelCheckerTestCase {

	public Github1394kTest() {
		super("Github1394Inst", new String[] { "-config", "Github1394k.cfg" }, EC.ExitStatus.SUCCESS);
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
		assertTrue(recorder.recorded(EC.TLC_SUCCESS));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "4", "3", "0"));
	}
}
