package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

// INVARIANT BoxTypeOK where THEOREM BoxTypeOK == []TypeOK
public class Github1394jTest extends ModelCheckerTestCase {

	public Github1394jTest() {
		super("Github1394", new String[] { "-config", "Github1394j.cfg" }, EC.ExitStatus.FAILURE_SAFETY_EVAL);
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
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INVARIANT_VIOLATED_LEVEL, "BoxTypeOK"));
	}
}
