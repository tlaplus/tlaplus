package tlc2.tool;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.TestPrintStream;
import util.ToolIO;

public class DiffTraceTwoStatesTest extends ModelCheckerTestCase {

	private TestPrintStream testPrintStream;

	public DiffTraceTwoStatesTest() {
		super("DiffTrace", new String[] { "-difftrace", "-config", "DiffTraceTwoStates.cfg" },
				ExitStatus.VIOLATION_SAFETY);
	}

	@Override
	public void beforeSetUp() {
		testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
	}

	@Test
	public void testSpec() {
		// The initial state lists all variables.
		testPrintStream.assertContains("/\\ a = 0\n/\\ b = 0\n/\\ c = 0\n/\\ d = 0\n\n"
				+ "State 2: <SetA line 6, col 9 to line 6, col 48 of module DiffTrace>\n");
	}
}
