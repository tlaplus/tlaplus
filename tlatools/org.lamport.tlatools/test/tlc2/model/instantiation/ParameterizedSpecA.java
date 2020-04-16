package tlc2.model.instantiation;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import util.ConfigCreatingModelCheckerTestCase;

/**
 * This is the unit test for ParameterizedInstantiation.tla's SpecA case.
 */
public class ParameterizedSpecA extends ConfigCreatingModelCheckerTestCase {
	public ParameterizedSpecA() {
		super("ParameterizedInstantiation", "SPECIFICATION\nSpecA\n");
	}
	
	@Test
	public void testSpecA() throws Exception {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
	}
}
