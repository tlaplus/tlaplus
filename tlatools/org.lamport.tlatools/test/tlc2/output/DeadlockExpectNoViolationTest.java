package tlc2.output;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.impl.ModelConfig.ModelResult;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Test for when the model deadlocks but no violations were expected.
 */
public class DeadlockExpectNoViolationTest extends ModelCheckerTestCase {
  public DeadlockExpectNoViolationTest() {
		super("Deadlock", "expect", new String[] {"-config", "DeadlockExpectNoViolation.cfg"}, ExitStatus.VIOLATION_DEADLOCK);
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
