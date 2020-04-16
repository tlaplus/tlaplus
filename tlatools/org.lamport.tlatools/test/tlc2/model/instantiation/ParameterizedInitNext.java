package tlc2.model.instantiation;

import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import util.ConfigCreatingModelCheckerTestCase;

/**
 * This is the unit test for ParameterizedInstantiation.tla's Init-Next case.
 */
public class ParameterizedInitNext extends ConfigCreatingModelCheckerTestCase {
	public ParameterizedInitNext() {
		super("ParameterizedInstantiation", "INIT\nInit\nNEXT\nNext\n");
	}
	
	@Test
	public void testInitNext() throws Exception {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
	}
}
