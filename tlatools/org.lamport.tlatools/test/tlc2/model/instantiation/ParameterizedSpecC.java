package tlc2.model.instantiation;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import util.ConfigCreatingModelCheckerTestCase;

/**
 * This is the unit test for ParameterizedInstantiation.tla's SpecC.
 */
public class ParameterizedSpecC extends ConfigCreatingModelCheckerTestCase {
	public ParameterizedSpecC() {
		super("ParameterizedInstantiation", "SPECIFICATION\nSpecC\n");
	}
	
	@Test
	public void testSpecC() throws Exception {
		assertTrue(recorder.recorded(EC.TLC_CONFIG_SPEC_IS_TRIVIAL));
		setExitStatus(151);
	}
}
