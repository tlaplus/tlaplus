package tlc2.output;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.impl.ModelConfig.ModelResult;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Test for when the model violates a liveness property but no violations were expected.
 */
public class LivenessViolationExpectNoViolationTest extends ModelCheckerTestCase {
  public LivenessViolationExpectNoViolationTest() {
		super("LivenessViolation", "expect", new String[] {"-config", "LivenessViolationExpectNoViolation.cfg"}, ExitStatus.VIOLATION_LIVENESS);
  }

  @Override
  public boolean checkDeadLock() {
    return true;
  }

	@Test
	public void testSpec() {
	  assertEquals(ModelResult.NO_VIOLATION, tlc.getExpectedModelResult());
	}
}
