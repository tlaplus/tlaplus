package tlc2;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assume.assumeTrue;

import org.junit.Test;

public class TestCommandLineOptions
{
	@Test
	public void TestSimulateFlag()
	{
		String[] args = new String[]{"-simulate", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.SimulationMode.isPresent());
		assertTrue(actual.SimulationBehaviorCountLimit.isEmpty());
		assertTrue(actual.SimulationTraceFile.isEmpty());

		assertTrue(actual.SimulationMode.get());
	}

	@Test
	public void TestSimulateFlagWithBehaviorCountLimit()
	{
		final long expected = 1234;
		String[] args = new String[]{"-simulate", "num=" + expected, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();
		
		assertTrue(actual.SimulationMode.isPresent());
		assertTrue(actual.SimulationTraceFile.isEmpty());
		assertTrue(actual.SimulationMode.get());
		assertTrue(actual.SimulationBehaviorCountLimit.isPresent());
		assertEquals(expected, actual.SimulationBehaviorCountLimit.get().longValue());
	}
	
	@Test
	public void TestSimulateFlagWithTraceFile()
	{
		final String expected = "/path/to/file";
		String[] args = new String[]{"-simulate", "file=" + expected, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();
		
		assertTrue(actual.SimulationMode.isPresent());
		assertTrue(actual.SimulationMode.get());
		assertTrue(actual.SimulationBehaviorCountLimit.isEmpty());
		assertTrue(actual.SimulationTraceFile.isPresent());
		assertEquals(expected, actual.SimulationTraceFile.get());
	}
	
	@Test
	public void TestSimulateFlagWithBehaviorCountLimitAndTraceFile()
	{
		final long expectedLimit = 1234;
		final String expectedPath = "/path/to/file";
		String[] args = new String[]{"-simulate", "file=" + expectedPath + ",num=" + expectedLimit, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();
		
		assertTrue(actual.SimulationMode.isPresent());
		assertTrue(actual.SimulationMode.get());
		assertTrue(actual.SimulationTraceFile.isPresent());
		assertEquals(expectedPath, actual.SimulationTraceFile.get());

		assertTrue(actual.SimulationMode.isPresent());
		assertTrue(actual.SimulationMode.get());
		assertTrue(actual.SimulationBehaviorCountLimit.isPresent());
		assertEquals(expectedLimit, actual.SimulationBehaviorCountLimit.get().longValue());
	}

	@Test
	public void TestSimulateFlagWithBehaviorCountLimitAndTraceFileReverse()
	{
		final long expectedLimit = 1234;
		final String expectedPath = "/path/to/file";
		String[] args = new String[]{"-simulate", "num=" + expectedLimit + ",file=" + expectedPath, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();
		
		assertTrue(actual.SimulationMode.isPresent());
		assertTrue(actual.SimulationMode.get());
		assertTrue(actual.SimulationTraceFile.isPresent());
		assertEquals(expectedPath, actual.SimulationTraceFile.get());

		assertTrue(actual.SimulationMode.isPresent());
		assertTrue(actual.SimulationMode.get());
		assertTrue(actual.SimulationBehaviorCountLimit.isPresent());
		assertEquals(expectedLimit, actual.SimulationBehaviorCountLimit.get().longValue());
	}
	
	@Test
	/**
	 * This is a regression test to ensure the strange -simulate parsing semantics
	 * are maintained (see top comment in CommandLineOptions.java for details).
	 */
	public void TestOddSimulateSemantics()
	{
		final long expectedLimit = 1234;
		final String expectedPath = "/path/to/file";
		String[] args = new String[]{"-simulate", "num=" + expectedLimit + ",file=" + expectedPath};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.SimulationMode.isPresent());
		assertTrue(actual.SimulationBehaviorCountLimit.isEmpty());
		assertTrue(actual.SimulationTraceFile.isEmpty());
		assertTrue(actual.MainSpecFilePath.isPresent());
		
		args = new String[]{"test.tla", "-simulate", "num=" + expectedLimit + ",file=" + expectedPath};
		result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
	}

	@Test
	public void TestModelCheckFlag()
	{
		String[] args = new String[]{"-modelcheck", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.ModelCheck.isPresent());
		assertTrue(actual.ModelCheck.get());
	}
	
	@Test
	public void TestOnlyPrintStateTraceDiffsFlag()
	{
		String[] args = new String[]{"-difftrace", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.OnlyPrintStateTraceDiffs.isPresent());
		assertTrue(actual.OnlyPrintStateTraceDiffs.get());
	}

	@Test
	public void TestDeadlockFlag()
	{
		String[] args = new String[]{"-deadlock", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.CheckDeadlock.isPresent());
		assertFalse(actual.CheckDeadlock.get());
	}
	
	@Test
	public void TestCleanStateDirectoryFlag()
	{
		String[] args = new String[]{"-cleanup", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.CleanStatesDirectory.isPresent());
		assertTrue(actual.CleanStatesDirectory.get());
	}

	@Test
	public void TestNoWarningFlag()
	{
		String[] args = new String[]{"-nowarning", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.PrintWarnings.isPresent());
		assertFalse(actual.PrintWarnings.get());
	}

	@Test
	public void TestGZipFlag()
	{
		String[] args = new String[]{"-gzip", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.UseGZip.isPresent());
		assertTrue(actual.UseGZip.get());
	}

	@Test
	public void TestTerseOutputFlag()
	{
		String[] args = new String[]{"-terse", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.ExpandValuesInPrintStatements.isPresent());
		assertFalse(actual.ExpandValuesInPrintStatements.get());
	}

	@Test
	public void TestContinueAfterInvariantViolationFlag()
	{
		String[] args = new String[]{"-continue", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.ContinueAfterInvariantViolation.isPresent());
		assertTrue(actual.ContinueAfterInvariantViolation.get());
	}

	@Test
	public void TestViewFlag()
	{
		String[] args = new String[]{"-view", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.UseView.isPresent());
		assertTrue(actual.UseView.get());
	}

	@Test
	public void TestDebugFlag()
	{
		String[] args = new String[]{"-debug", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.Debug.isPresent());
		assertTrue(actual.Debug.get());
	}

	@Test
	public void TestToolOutputFlag()
	{
		String[] args = new String[]{"-tool", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.UseToolOutputFormat.isPresent());
		assertTrue(actual.UseToolOutputFormat.get());
	}

	@Test
	public void TestGenerateErrorTraceSpecFlag()
	{
		String[] args = new String[]{"-generateSpecTE", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.GenerateErrorTraceSpec.isPresent());
		assertTrue(actual.GenerateErrorTraceSpec.get());
		assertTrue(actual.CreateMonolithErrorTraceSpec.isPresent());
		assertTrue(actual.CreateMonolithErrorTraceSpec.get());
	}

	@Test
	public void TestGenerateErrorTraceSpecFlagWithNoMonolithValue()
	{
		String[] args = new String[]{"-generateSpecTE", "nomonolith", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.GenerateErrorTraceSpec.isPresent());
		assertTrue(actual.GenerateErrorTraceSpec.get());
		assertTrue(actual.CreateMonolithErrorTraceSpec.isPresent());
		assertFalse(actual.CreateMonolithErrorTraceSpec.get());
	}

	@Test
	public void TestHelpFlag()
	{
		String[] args = new String[]{"-help", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.PrintHelpText.isPresent());
		assertTrue(actual.PrintHelpText.get());
	}

	@Test
	public void TestShortHelpFlag()
	{
		String[] args = new String[]{"-h", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.PrintHelpText.isPresent());
		assertTrue(actual.PrintHelpText.get());
	}

	@Test
	public void TestLivenessCheckOption()
	{
		final String expectedValue = "final";
		String[] args = new String[]{"-lncheck", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.LivenessCheck.isPresent());
		assertEquals(expectedValue, actual.LivenessCheck.get());
	}

	@Test
	public void TestInvalidLivenessCheckOption()
	{
		String[] args = new String[]{"test.tla", "-lncheck"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("lncheck"));
	}
	
	@Test
	public void TestLivenessCheckOptionWithoutSpec()
	{
		final String expectedValue = "final";
		String[] args = new String[]{"-lncheck", expectedValue};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.LivenessCheck.isPresent());
		assertEquals(expectedValue, actual.LivenessCheck.get());
	}
}