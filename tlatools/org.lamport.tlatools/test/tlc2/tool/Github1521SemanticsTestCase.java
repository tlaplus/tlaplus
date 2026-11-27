package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public abstract class Github1521SemanticsTestCase extends ModelCheckerTestCase {

	protected Github1521SemanticsTestCase(final String variant) {
		super("Github1521Semantics", new String[] { "-config", "Github1521" + variant + ".cfg" });
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}

	@Test
	public void testSpec() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recorded(EC.TLC_SUCCESS));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "3", "2", "0"));
	}
}
