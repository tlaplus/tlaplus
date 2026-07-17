package tlc2.output;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.impl.ModelConfig.ModelResult;
import tlc2.tool.liveness.ModelCheckerTestCase;

/**
 * Test for when the model deadlocks and deadlock was expected.
 */
public class DeadlockExpectDeadlockTest extends ModelCheckerTestCase {
  public DeadlockExpectDeadlockTest() {
		super("Deadlock", "expect", new String[] {"-config", "DeadlockExpectDeadlock.cfg"}, ExitStatus.SUCCESS);
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