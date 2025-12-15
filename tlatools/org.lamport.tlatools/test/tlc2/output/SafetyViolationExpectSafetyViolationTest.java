package tlc2.output;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.impl.ModelConfig.ModelResult;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Test for when the model violates a safety property and a safety violation was expected.
 */
public class SafetyViolationExpectSafetyViolationTest extends ModelCheckerTestCase {
  public SafetyViolationExpectSafetyViolationTest() {
		super("SafetyViolation", "expect", new String[] {"-config", "SafetyViolationExpectSafetyViolation.cfg"}, ExitStatus.SUCCESS);
  }

  @Override
  public boolean checkDeadLock() {
    return true;
  }

	@Test
	public void testSpec() {
	  assertEquals(ModelResult.SAFETY_VIOLATION, tlc.getExpectedModelResult());
	}
}
