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

		args = new String[]{"-simulate", "num=" + expectedLimit + ",file=" + expectedPath, "test.tla"};

		result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		actual = result.Options.get();
		
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

		assertTrue(actual.DoNotCheckDeadlock.isPresent());
		assertTrue(actual.DoNotCheckDeadlock.get());
	}
	
	@Test
	public void TestCleanStateDirectoryFlag()
	{
		String[] args = new String[]{"-cleanup", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.CleanStateDirectory.isPresent());
		assertTrue(actual.CleanStateDirectory.get());
	}

	@Test
	public void TestNoWarningFlag()
	{
		String[] args = new String[]{"-nowarning", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.DoNotPrintWarnings.isPresent());
		assertTrue(actual.DoNotPrintWarnings.get());
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

		assertTrue(actual.TerseOutput.isPresent());
		assertTrue(actual.TerseOutput.get());
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
}