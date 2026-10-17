package tlc2.tool;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.TestPrintStream;
import util.ToolIO;

public class DiffTraceThreeStatesTest extends ModelCheckerTestCase {

	private TestPrintStream testPrintStream;

	public DiffTraceThreeStatesTest() {
		super("DiffTrace", new String[] { "-difftrace", "-config", "DiffTraceThreeStates.cfg" },
				ExitStatus.VIOLATION_SAFETY);
	}

	@Override
	public void beforeSetUp() {
		testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
	}

	@Test
	public void testSpec() {
		testPrintStream.assertContains("State 2: <SetA line 6, col 9 to line 6, col 48 of module DiffTrace>\n"
				+ "/\\ a = 1\n\n"
				+ "State 3: <SetB line 7, col 9 to line 7, col 57 of module DiffTrace>\n"
				+ "/\\ a = 1\n/\\ b = 1\n/\\ c = 0\n/\\ d = 0\n");
	}
}
