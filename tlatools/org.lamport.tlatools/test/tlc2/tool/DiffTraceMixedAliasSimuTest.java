package tlc2.tool;

import org.junit.Test;

import tlc2.output.EC.ExitStatus;
import tlc2.tool.liveness.ModelCheckerTestCase;
import util.TestPrintStream;
import util.ToolIO;

public class DiffTraceMixedAliasSimuTest extends ModelCheckerTestCase {

	private TestPrintStream testPrintStream;

	public DiffTraceMixedAliasSimuTest() {
		super("DiffTraceAlias",
				new String[] { "-difftrace", "-config", "DiffTraceMixedAlias.cfg", "-simulate", "num=1" },
				ExitStatus.VIOLATION_SAFETY);
	}

	@Override
	public void beforeSetUp() {
		testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
	}

	@Test
	public void testSpec() {
		// a changes from "none" to 1. States 4 and 5 are not aliased.
		testPrintStream.assertContains("State 2: <SetA line 6, col 9 to line 6, col 48 of module DiffTrace>\n"
				+ "/\\ a = 1\n\n"
				+ "State 3: <SetB line 7, col 9 to line 7, col 57 of module DiffTrace>\n"
				+ "/\\ ab = 1\n\n"
				+ "State 4: <SetC line 8, col 9 to line 8, col 57 of module DiffTrace>\n"
				+ "/\\ c = 1\n\n"
				+ "State 5: <SetD line 9, col 9 to line 9, col 57 of module DiffTrace>\n"
				+ "/\\ d = 1\n");
	}
}
