package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github1515InitialSafeTest extends ModelCheckerTestCase {

	public Github1515InitialSafeTest() {
		super("Github1515InitialSafe", new String[] { "-config", "Github1515InitialSafe.cfg" }, ExitStatus.SUCCESS);
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertFalse(recorder.recorded(EC.TLC_INVARIANT_VIOLATED_INITIAL));
		assertFalse(recorder.recorded(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR));
		assertFalse(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
	}

	@Override
	protected boolean runWithDebugger() {
		return false;
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}
}
