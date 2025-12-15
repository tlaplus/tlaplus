package tlc2.output;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.impl.ModelConfig.ModelResult;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Test for when the model violates an assertion but no violations were expected.
 */
public class AssertViolationExpectNoViolationTest extends ModelCheckerTestCase {
  public AssertViolationExpectNoViolationTest() {
		super("AssertViolation", "expect", new String[] {"-config", "AssertViolationExpectNoViolation.cfg"}, ExitStatus.VIOLATION_ASSERT);
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
