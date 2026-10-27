package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

// PROPERTY SpecTypeOK where THEOREM SpecTypeOK == Spec => []TypeOK
public class Github1394bTest extends ModelCheckerTestCase {

	public Github1394bTest() {
		super("Github1394", new String[] { "-config", "Github1394b.cfg" }, EC.ExitStatus.SUCCESS);
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
