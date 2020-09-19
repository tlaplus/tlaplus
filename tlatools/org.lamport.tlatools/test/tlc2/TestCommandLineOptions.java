package tlc2;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assume.assumeTrue;

import java.util.ArrayList;

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

		assertTrue(actual.MainSpecFilePath.isPresent());
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
		
		assertTrue(actual.MainSpecFilePath.isPresent());
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
		
		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.GenerateErrorTraceSpec.isPresent());
		assertTrue(actual.GenerateErrorTraceSpec.get());
		assertTrue(actual.CreateMonolithErrorTraceSpec.isPresent());
		assertFalse(actual.CreateMonolithErrorTraceSpec.get());
	}

	@Test
	public void TestHelpFlag()
	{
		String[] args = new String[]{"-help"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.HelpRequest);
		assertTrue(result.Options.isEmpty());
	}

	@Test
	public void TestShortHelpFlag()
	{
		String[] args = new String[]{"-h"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.HelpRequest);
		assertTrue(result.Options.isEmpty());
	}

	@Test
	public void TestHelpFlagWithGibberish()
	{
		String[] args = new String[]{"-h", "NotAnOption", "AlsoNotAnOption"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.HelpRequest);
		assertTrue(result.Options.isEmpty());
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

		assertTrue(actual.MainSpecFilePath.isPresent());
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
	public void TestConfigOption()
	{
		final String expectedValue = "configFile.cfg";
		String[] args = new String[]{"-config", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.ConfigurationFilePath.isPresent());
		assertEquals(expectedValue, actual.ConfigurationFilePath.get());
	}

	@Test
	public void TestInvalidConfigOption()
	{
		String[] args = new String[]{"test.tla", "-config"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("config"));
	}
	
	@Test
	public void TestDumpOption()
	{
		final String expectedValue = "dump.out";
		String[] args = new String[]{"-dump", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.DumpFilePath.isPresent());
		assertEquals(expectedValue, actual.DumpFilePath.get());
		assertTrue(actual.DumpFileOptions.isEmpty());
	}
	
	@Test
	public void TestInvalidDumpOption()
	{
		String[] args = new String[]{"test.tla", "-dump"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("dump"));
	}
	
	@Test
	public void TestDumpFileControlsOption()
	{
		final String[] possibleFlags = new String[]{"colorize", "actionlabels", "snapshot"};
		final String expectedFileValue = "dump.out";
		
		// Iterate through all possibleFlags subsets of at least size 1
		for (int bitmask = 0; bitmask < (1 << possibleFlags.length); bitmask++)
		{
			ArrayList<String> flagList = new ArrayList<String>(possibleFlags.length);
			flagList.add("dot");

			for (int i = 0; i < possibleFlags.length; i++)
			{
				if ((bitmask & (1 << i)) != 0)
				{
					flagList.add(possibleFlags[i]);
				}
			}
			
			final String flags = String.join(",", flagList);
			final String[] args = new String[]{"-dump", flags, expectedFileValue, "test.tla"};

			CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
			assertTrue(result.Success);
			assertTrue(result.Options.isPresent());
			CommandLineOptions actual = result.Options.get();

			assertTrue(actual.MainSpecFilePath.isPresent());
			assertTrue(actual.DumpFilePath.isPresent());
			assertEquals(expectedFileValue, actual.DumpFilePath.get());
			assertTrue(actual.DumpFileOptions.isPresent());
			CommandLineOptions.DumpFileControls actualControls = actual.DumpFileOptions.get();
			
			if (flagList.contains("colorize"))
			{
				assertTrue(actualControls.Colorize);
			}
			
			if (flagList.contains("actionlabels"))
			{
				assertTrue(actualControls.ActionLabels);
			}
			
			if (flagList.contains("snapshot"))
			{
				assertTrue(actualControls.Snapshot);
			}
		}
	}
	
	@Test
	public void TestCoverageOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-coverage", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.CoverageIntervalInMinutes.isPresent());
		assertEquals(expectedValue, actual.CoverageIntervalInMinutes.get());
	}
	
	@Test
	public void TestInvalidCoverageOption()
	{
		String[] args = new String[]{"test.tla", "-coverage"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("coverage"));
	}
	
	@Test
	public void TestNotNumberCoverageOption()
	{
		String[] args = new String[]{"-coverage", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("coverage"));
	}
	
	@Test
	public void TestCheckpointOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-checkpoint", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.CheckpointIntervalInMinutes.isPresent());
		assertEquals(expectedValue, actual.CheckpointIntervalInMinutes.get());
	}
	
	@Test
	public void TestInvalidCheckpointOption()
	{
		String[] args = new String[]{"test.tla", "-checkpoint"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("checkpoint"));
	}
	
	@Test
	public void TestNotNumberCheckpointOption()
	{
		String[] args = new String[]{"-checkpoint", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("checkpoint"));
	}
	
	@Test
	public void TestDepthOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-depth", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.SimulationTraceDepthLimit.isPresent());
		assertEquals(expectedValue, actual.SimulationTraceDepthLimit.get());
	}
	
	@Test
	public void TestInvalidDepthOption()
	{
		String[] args = new String[]{"test.tla", "-depth"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("depth"));
	}
	
	@Test
	public void TestNotNumberDepthOption()
	{
		String[] args = new String[]{"-depth", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("depth"));
	}
	
	@Test
	public void TestSeedOption()
	{
		final Long expectedValue = 2L;
		String[] args = new String[]{"-seed", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.Seed.isPresent());
		assertEquals(expectedValue, actual.Seed.get());
	}
	
	@Test
	public void TestInvalidSeedOption()
	{
		String[] args = new String[]{"test.tla", "-seed"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("seed"));
	}
	
	@Test
	public void TestNotNumberSeedOption()
	{
		String[] args = new String[]{"-seed", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("seed"));
	}
	
	@Test
	public void TestArilOption()
	{
		final Long expectedValue = 2L;
		String[] args = new String[]{"-aril", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.Aril.isPresent());
		assertEquals(expectedValue, actual.Aril.get());
	}
	
	@Test
	public void TestInvalidArilOption()
	{
		String[] args = new String[]{"test.tla", "-aril"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("aril"));
	}
	
	@Test
	public void TestNotNumberArilOption()
	{
		String[] args = new String[]{"-aril", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("aril"));
	}
	
	@Test
	public void TestMaxSetSizeOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-maxSetSize", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.MaxSetSize.isPresent());
		assertEquals(expectedValue, actual.MaxSetSize.get());
	}
	
	@Test
	public void TestInvalidMaxSetSizeOption()
	{
		String[] args = new String[]{"test.tla", "-maxSetSize"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("maxSetSize"));
	}
	
	@Test
	public void TestNotNumberMaxSetSizeOption()
	{
		String[] args = new String[]{"-maxSetSize", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("maxSetSize"));
	}

	@Test
	public void TestRecoverOption()
	{
		final String expectedValue = "somename";
		String[] args = new String[]{"-recover", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.RecoveryId.isPresent());
		assertEquals(expectedValue, actual.RecoveryId.get());
	}

	@Test
	public void TestInvalidRecoverOption()
	{
		String[] args = new String[]{"test.tla", "-recover"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("recover"));
	}

	@Test
	public void TestMetadataDirectoryOption()
	{
		final String expectedValue = "somename";
		String[] args = new String[]{"-metadir", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.MetadataDirectoryPath.isPresent());
		assertEquals(expectedValue, actual.MetadataDirectoryPath.get());
	}

	@Test
	public void TestInvalidMetadataDirectoryOption()
	{
		String[] args = new String[]{"test.tla", "-metadir"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("metadir"));
	}

	@Test
	public void TestUserFileOption()
	{
		final String expectedValue = "somename";
		String[] args = new String[]{"-userFile", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.UserOutputFilePath.isPresent());
		assertEquals(expectedValue, actual.UserOutputFilePath.get());
	}

	@Test
	public void TestInvalidUserFileOption()
	{
		String[] args = new String[]{"test.tla", "-userFile"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("userFile"));
	}

	@Test
	public void TestAutoWorkersOption()
	{
		final String expectedValue = "auto";
		String[] args = new String[]{"-workers", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.TlcWorkerThreadOptions.isPresent());
		assertTrue(actual.TlcWorkerThreadOptions.get().Automatic);
		assertTrue(actual.TlcWorkerThreadOptions.get().ThreadCount.isEmpty());
	}

	@Test
	public void TestManualAutoWorkersOption()
	{
		final Integer expectedValue = 4;
		String[] args = new String[]{"-workers", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.TlcWorkerThreadOptions.isPresent());
		assertFalse(actual.TlcWorkerThreadOptions.get().Automatic);
		assertTrue(actual.TlcWorkerThreadOptions.get().ThreadCount.isPresent());
		assertEquals(expectedValue, actual.TlcWorkerThreadOptions.get().ThreadCount.get());
	}

	@Test
	public void TestInvalidWorkersOption()
	{
		String[] args = new String[]{"test.tla", "-workers"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("workers"));
	}

	@Test
	public void TestNotANumberWorkersOption()
	{
		String[] args = new String[]{"-workers", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("workers"));
	}
	
	@Test
	public void TestDfidOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-dfid", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.DfidStartingDepth.isPresent());
		assertEquals(expectedValue, actual.DfidStartingDepth.get());
	}
	
	@Test
	public void TestInvalidDfidOption()
	{
		String[] args = new String[]{"test.tla", "-dfid"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("dfid"));
	}
	
	@Test
	public void TestNotNumberDfidOption()
	{
		String[] args = new String[]{"-dfid", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("dfid"));
	}
	
	@Test
	public void TestFpOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-fp", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.FingerprintFunctionIndex.isPresent());
		assertEquals(expectedValue, actual.FingerprintFunctionIndex.get());
	}
	
	@Test
	public void TestInvalidFpOption()
	{
		String[] args = new String[]{"test.tla", "-fp"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fp"));
	}
	
	@Test
	public void TestNotNumberFpOption()
	{
		String[] args = new String[]{"-fp", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fp"));
	}
	
	@Test
	public void TestFpMemOption()
	{
		final Double expectedValue = 1.0;
		String[] args = new String[]{"-fpmem", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.FingerprintSetMemoryUsePercentage.isPresent());
		assertEquals(expectedValue, actual.FingerprintSetMemoryUsePercentage.get());
	}
	
	@Test
	public void TestInvalidFpMemOption()
	{
		String[] args = new String[]{"test.tla", "-fpmem"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fpmem"));
	}
	
	@Test
	public void TestNotNumberFpMemOption()
	{
		String[] args = new String[]{"-fpmem", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fpmem"));
	}
	
	@Test
	public void TestFpBitsOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-fpbits", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertTrue(actual.FingerprintBits.isPresent());
		assertEquals(expectedValue, actual.FingerprintBits.get());
	}
	
	@Test
	public void TestInvalidFpBitsOption()
	{
		String[] args = new String[]{"test.tla", "-fpbits"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fpbits"));
	}
	
	@Test
	public void TestNotNumberFpBitsOption()
	{
		String[] args = new String[]{"-fpbits", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fpbits"));
	}
	
	@Test
	public void TestMainSpecOption()
	{
		final String expectedValue = "test.tla";
		String[] args = new String[]{expectedValue};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.Options.isPresent());
		CommandLineOptions actual = result.Options.get();

		assertTrue(actual.MainSpecFilePath.isPresent());
		assertEquals(expectedValue, actual.MainSpecFilePath.get());
	}
	
	@Test
	public void TestTwoMainSpecs()
	{
		String[] args = new String[]{"first.tla", "second.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
	}
}