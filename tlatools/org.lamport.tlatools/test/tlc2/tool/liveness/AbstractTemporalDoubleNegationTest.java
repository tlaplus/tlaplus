package tlc2.tool.liveness;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.output.EC;
import tlc2.output.EC.ExitStatus;

/**
 * Valid properties that must not produce the spurious counterexamples from
 * https://github.com/tlaplus/model-checker-hardening/issues/183.
 */
public abstract class AbstractTemporalDoubleNegationTest extends ModelCheckerTestCase {

	protected AbstractTemporalDoubleNegationTest(final String config) {
		super("TemporalDoubleNegation", new String[] { "-config", config }, ExitStatus.SUCCESS);
	}

	@Override
	protected boolean runWithDebugger() {
		return false;
	}

	@Override
	protected boolean noGenerateSpec() {
		return true;
	}

	@Override
	protected boolean doDump() {
		return false;
	}

	@Override
	protected boolean doDumpTrace() {
		return false;
	}

	@Override
	protected boolean doCoverage() {
		return false;
	}

	@Test
	public void testValidProperty() {
		assertTrue(recorder.recorded(EC.TLC_FINISHED));
		assertFalse(recorder.recorded(EC.GENERAL));
		assertFalse("A valid property must not produce a temporal violation", recorder.recorded(EC.TLC_TEMPORAL_PROPERTY_VIOLATED));
		assertFalse("A valid property must not produce a counterexample", recorder.recorded(EC.TLC_COUNTER_EXAMPLE));
		assertTrue(recorder.recorded(EC.TLC_SUCCESS));
	}
}
