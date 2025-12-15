package tlc2.output;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.impl.ModelConfig.ModelResult;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Test for when the model violates an assertion and an assert violation was expected.
 */
public class AssertViolationExpectAssertViolationTest extends ModelCheckerTestCase {
  public AssertViolationExpectAssertViolationTest() {
		super("AssertViolation", "expect", new String[] {"-config", "AssertViolationExpectAssertViolation.cfg"}, ExitStatus.SUCCESS);
  }

  @Override
  public boolean checkDeadLock() {
    return true;
  }

	@Test
	public void testSpec() {
	  assertEquals(ModelResult.ASSERT_VIOLATION, tlc.getExpectedModelResult());
	}
}
