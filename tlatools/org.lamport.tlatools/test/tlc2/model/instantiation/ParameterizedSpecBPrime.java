package tlc2.model.instantiation;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import util.ConfigCreatingModelCheckerTestCase;

/**
 * This is the unit test for ParameterizedInstantiation.tla's SpecB case plus a failing temporal check.
 */
public class ParameterizedSpecBPrime extends ConfigCreatingModelCheckerTestCase {
	public ParameterizedSpecBPrime() {
		super("ParameterizedInstantiation", "SPECIFICATION\nSpecB\nPROPERTY\nFalseAECheck\n");
	}
	
	@Test
	public void testSpecBPrime() throws Exception {
		assertTrue(recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		setExitStatus(13);
	}
}
