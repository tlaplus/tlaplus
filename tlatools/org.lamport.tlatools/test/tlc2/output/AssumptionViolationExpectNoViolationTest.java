package tlc2.output;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.impl.ModelConfig.ModelResult;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Test for when the model violates an assumption but no violations were expected.
 */
public class AssumptionViolationExpectNoViolationTest extends ModelCheckerTestCase {
  public AssumptionViolationExpectNoViolationTest() {
		super("AssumptionViolation", "expect", new String[] {"-config", "AssumptionViolationExpectNoViolation.cfg"}, ExitStatus.VIOLATION_ASSUMPTION);
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
