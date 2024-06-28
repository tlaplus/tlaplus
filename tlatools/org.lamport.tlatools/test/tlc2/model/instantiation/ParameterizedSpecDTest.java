package tlc2.model.instantiation;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import util.ConfigCreatingModelCheckerTestCase;

/**
 * This is the unit test for ParameterizedInstantiation.tla's SpecD.
 */
public class ParameterizedSpecDTest extends ConfigCreatingModelCheckerTestCase {
	public ParameterizedSpecDTest() {
		super("ParameterizedInstantiation", "SPECIFICATION\nSpecD\n");
	}
	
	@Test
	public void testSpecD() throws Exception {
		assertTrue(recorder.recorded(EC.TLC_CONFIG_SPEC_IS_TRIVIAL));
		setExitStatus(151);
	}
}
