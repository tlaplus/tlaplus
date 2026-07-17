package tlc2.output;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.impl.ModelConfig.ModelResult;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Test for when the model has no violations but a deadlock violation was expected.
 */
public class NoViolationExpectDeadlockViolationTest extends ModelCheckerTestCase {
  public NoViolationExpectDeadlockViolationTest() {
		super("NoViolation", "expect", new String[] {"-config", "NoViolationExpectDeadlockViolation.cfg"}, ExitStatus.VIOLATION_ASSUMPTION);
  }

  @Override
  public boolean checkDeadLock() {
    return true;
  }

	@Test
	public void testSpec() {
	  assertEquals(ModelResult.DEADLOCK_VIOLATION, tlc.getExpectedModelResult());
	}
}