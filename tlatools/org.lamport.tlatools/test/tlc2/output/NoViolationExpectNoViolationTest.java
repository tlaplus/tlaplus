package tlc2.output;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.impl.ModelConfig.ModelResult;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Test for when the model has no violations and no violations are expected.
 */
public class NoViolationExpectNoViolationTest extends ModelCheckerTestCase {
  public NoViolationExpectNoViolationTest() {
		super("NoViolation", "expect", new String[] {"-config", "NoViolationExpectNoViolation.cfg"}, ExitStatus.SUCCESS);
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