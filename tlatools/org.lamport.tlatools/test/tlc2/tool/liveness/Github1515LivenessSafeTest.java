package tlc2.tool.liveness;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;

public class Github1515LivenessSafeTest extends ModelCheckerTestCase {

	public Github1515LivenessSafeTest() {
		super("Github1515LivenessSafe", new String[] { "-config", "Github1515LivenessSafe.cfg" }, ExitStatus.SUCCESS);
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertFalse(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertFalse(recorder.recorded(EC.TLC_INVARIANT_VIOLATED_INITIAL));
		assertFalse(recorder.recorded(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR));
	}
}
