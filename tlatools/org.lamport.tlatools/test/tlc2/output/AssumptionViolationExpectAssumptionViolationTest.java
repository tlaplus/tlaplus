package tlc2.output;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.impl.ModelConfig.ModelResult;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Test for when the model violates an assumption and an assumption violation was expected.
 */
public class AssumptionViolationExpectAssumptionViolationTest extends ModelCheckerTestCase {
  public AssumptionViolationExpectAssumptionViolationTest() {
		super("AssumptionViolation", "expect", new String[] {"-config", "AssumptionViolationExpectAssumptionViolation.cfg"}, ExitStatus.SUCCESS);
  }

  @Override
  public boolean checkDeadLock() {
    return true;
  }

	@Test
	public void testSpec() {
	  assertEquals(ModelResult.ASSUMPTION_VIOLATION, tlc.getExpectedModelResult());
	}
}