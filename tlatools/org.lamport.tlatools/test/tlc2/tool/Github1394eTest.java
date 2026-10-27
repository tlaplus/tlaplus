package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

// PROPERTY SpecReachesFive where THEOREM SpecReachesFive == Spec => <>(x = 5)
public class Github1394eTest extends ModelCheckerTestCase {

	public Github1394eTest() {
		super("Github1394", new String[] { "-config", "Github1394e.cfg" }, EC.ExitStatus.VIOLATION_LIVENESS);
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
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
	}
}
