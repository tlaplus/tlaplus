package tlc2.model.instantiation;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import util.ConfigCreatingModelCheckerTestCase;

/**
 * This is the unit test for ParameterizedInstantiation.tla's SpecB case.
 */
public class ParameterizedSpecBTest extends ConfigCreatingModelCheckerTestCase {
	public ParameterizedSpecBTest() {
		super("ParameterizedInstantiation", "SPECIFICATION\nSpecB\nPROPERTY\nAECheck\n");
	}
	
	@Test
	public void testSpecB() throws Exception {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
	}
}
