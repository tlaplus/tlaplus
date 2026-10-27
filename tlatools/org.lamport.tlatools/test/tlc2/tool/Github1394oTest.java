package tlc2.tool;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

// INVARIANT Small where the LEMMA comes from INSTANCE Github1394
public class Github1394oTest extends ModelCheckerTestCase {

	public Github1394oTest() {
		super("Github1394Inst", new String[] { "-config", "Github1394o.cfg" }, EC.ExitStatus.VIOLATION_SAFETY);
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
		assertTrue(recorder.recordedWithStringValue(EC.TLC_INVARIANT_VIOLATED_BEHAVIOR, "Small"));
	}
}
