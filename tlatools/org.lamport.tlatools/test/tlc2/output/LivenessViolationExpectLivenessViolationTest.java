package tlc2.output;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.impl.ModelConfig.ModelResult;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Test for when the model violates a liveness property and a liveness violation was expected.
 */
public class LivenessViolationExpectLivenessViolationTest extends ModelCheckerTestCase {
  public LivenessViolationExpectLivenessViolationTest() {
		super("LivenessViolation", "expect", new String[] {"-config", "LivenessViolationExpectLivenessViolation.cfg"}, ExitStatus.SUCCESS);
  }

  @Override
  public boolean checkDeadLock() {
    return true;
  }

	@Test
	public void testSpec() {
	  assertEquals(ModelResult.LIVENESS_VIOLATION, tlc.getExpectedModelResult());
	}
}
