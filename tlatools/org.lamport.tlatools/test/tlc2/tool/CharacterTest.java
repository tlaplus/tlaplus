package tlc2.tool;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class CharacterTest extends ModelCheckerTestCase {
	public CharacterTest() {
		super("CharacterTest", new String[] { "-config", "CharacterTest.tla"});
	}

	@Test
	public void testSpec() {
		// Simulation has finished and generated states
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertTrue(recorder.recordedWithStringValue(EC.TLC_SEARCH_DEPTH, "0"));
		assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "0", "0", "0"));
	}
}
