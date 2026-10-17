package tlc2.tool;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.TestPrintStream;
import util.ToolIO;

public class DiffTraceAliasSimuTest extends ModelCheckerTestCase {

	private TestPrintStream testPrintStream;

	public DiffTraceAliasSimuTest() {
		super("DiffTraceAlias", new String[] { "-difftrace", "-simulate", "num=1" }, ExitStatus.VIOLATION_SAFETY);
	}

	@Override
	public void beforeSetUp() {
		testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
	}

	@Test
	public void testSpec() {
		// ab, which is not a variable, is listed only when it changes.
		testPrintStream.assertContains("State 2: <SetA line 6, col 9 to line 6, col 48 of module DiffTrace>\n"
				+ "/\\ a = 1\n/\\ ab = 1\n\n"
				+ "State 3: <SetB line 7, col 9 to line 7, col 57 of module DiffTrace>\n"
				+ "/\\ b = 1\n/\\ ab = 2\n\n"
				+ "State 4: <SetC line 8, col 9 to line 8, col 57 of module DiffTrace>\n"
				+ "/\\ c = 1\n\n"
				+ "State 5: <SetD line 9, col 9 to line 9, col 57 of module DiffTrace>\n"
				+ "/\\ d = 1\n");
	}
}
