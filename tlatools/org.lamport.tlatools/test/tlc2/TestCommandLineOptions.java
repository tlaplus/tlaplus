package tlc2;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import org.junit.Test;

import tlc2.tool.fp.MultiFPSet;
import tlc2.util.FP64;
import util.FileUtil;
import util.TLAConstants;

import java.util.ArrayList;
import java.util.Optional;

public class TestCommandLineOptions
{
	/**
	 * Unit tests for CommandLineOptions.Parse function
	 */

	@Test
	public void testSimulateFlag()
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
	public void testSimulateFlagWithBehaviorCountLimit()
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
	public void testSimulateFlagWithTraceFile()
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
	public void testSimulateFlagWithBehaviorCountLimitAndTraceFile()
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
	public void testSimulateFlagWithBehaviorCountLimitAndTraceFileReverse()
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
	public void testOddSimulateSemantics()
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
	public void testModelCheckFlag()
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
	public void testOnlyPrintStateTraceDiffsFlag()
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
	public void testDeadlockFlag()
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
	public void testCleanStateDirectoryFlag()
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
	public void testNoWarningFlag()
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
	public void testGZipFlag()
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
	public void testTerseOutputFlag()
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
	public void testContinueAfterInvariantViolationFlag()
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
	public void testViewFlag()
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
	public void testDebugFlag()
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
	public void testToolOutputFlag()
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
	public void testGenerateErrorTraceSpecFlag()
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
	public void testGenerateErrorTraceSpecFlagWithNoMonolithValue()
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
	public void testHelpFlag()
	{
		String[] args = new String[]{"-help"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.HelpRequest);
		assertTrue(result.Options.isEmpty());
	}

	@Test
	public void testShortHelpFlag()
	{
		String[] args = new String[]{"-h"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.HelpRequest);
		assertTrue(result.Options.isEmpty());
	}

	@Test
	public void testHelpFlagWithGibberish()
	{
		String[] args = new String[]{"-h", "NotAnOption", "AlsoNotAnOption"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertTrue(result.Success);
		assertTrue(result.HelpRequest);
		assertTrue(result.Options.isEmpty());
	}

	@Test
	public void testLivenessCheckOption()
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
	public void testInvalidLivenessCheckOption()
	{
		String[] args = new String[]{"test.tla", "-lncheck"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("lncheck"));
	}

	@Test
	public void testConfigOption()
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
	public void testInvalidConfigOption()
	{
		String[] args = new String[]{"test.tla", "-config"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("config"));
	}
	
	@Test
	public void testDumpOption()
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
	public void testInvalidDumpOption()
	{
		String[] args = new String[]{"test.tla", "-dump"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("dump"));
	}
	
	@Test
	public void testDumpFileControlsOption()
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
	public void testCoverageOption()
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
	public void testInvalidCoverageOption()
	{
		String[] args = new String[]{"test.tla", "-coverage"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("coverage"));
	}
	
	@Test
	public void testNotNumberCoverageOption()
	{
		String[] args = new String[]{"-coverage", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("coverage"));
	}
	
	@Test
	public void testCheckpointOption()
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
	public void testInvalidCheckpointOption()
	{
		String[] args = new String[]{"test.tla", "-checkpoint"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("checkpoint"));
	}
	
	@Test
	public void testNotNumberCheckpointOption()
	{
		String[] args = new String[]{"-checkpoint", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("checkpoint"));
	}
	
	@Test
	public void testDepthOption()
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
	public void testInvalidDepthOption()
	{
		String[] args = new String[]{"test.tla", "-depth"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("depth"));
	}
	
	@Test
	public void testNotNumberDepthOption()
	{
		String[] args = new String[]{"-depth", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("depth"));
	}
	
	@Test
	public void testSeedOption()
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
	public void testInvalidSeedOption()
	{
		String[] args = new String[]{"test.tla", "-seed"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("seed"));
	}
	
	@Test
	public void testNotNumberSeedOption()
	{
		String[] args = new String[]{"-seed", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("seed"));
	}
	
	@Test
	public void testArilOption()
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
	public void testInvalidArilOption()
	{
		String[] args = new String[]{"test.tla", "-aril"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("aril"));
	}
	
	@Test
	public void testNotNumberArilOption()
	{
		String[] args = new String[]{"-aril", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("aril"));
	}
	
	@Test
	public void testMaxSetSizeOption()
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
	public void testInvalidMaxSetSizeOption()
	{
		String[] args = new String[]{"test.tla", "-maxSetSize"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("maxSetSize"));
	}
	
	@Test
	public void testNotNumberMaxSetSizeOption()
	{
		String[] args = new String[]{"-maxSetSize", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("maxSetSize"));
	}

	@Test
	public void testRecoverOption()
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
	public void testInvalidRecoverOption()
	{
		String[] args = new String[]{"test.tla", "-recover"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("recover"));
	}

	@Test
	public void testMetadataDirectoryOption()
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
	public void testInvalidMetadataDirectoryOption()
	{
		String[] args = new String[]{"test.tla", "-metadir"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("metadir"));
	}

	@Test
	public void testUserFileOption()
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
	public void testInvalidUserFileOption()
	{
		String[] args = new String[]{"test.tla", "-userFile"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("userFile"));
	}

	@Test
	public void testAutoWorkersOption()
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
	public void testManualAutoWorkersOption()
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
	public void testInvalidWorkersOption()
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
	public void testDfidOption()
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
	public void testInvalidDfidOption()
	{
		String[] args = new String[]{"test.tla", "-dfid"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("dfid"));
	}
	
	@Test
	public void testNotNumberDfidOption()
	{
		String[] args = new String[]{"-dfid", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("dfid"));
	}
	
	@Test
	public void testFpOption()
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
	public void testInvalidFpOption()
	{
		String[] args = new String[]{"test.tla", "-fp"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fp"));
	}
	
	@Test
	public void testNotNumberFpOption()
	{
		String[] args = new String[]{"-fp", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fp"));
	}
	
	@Test
	public void testFpMemOption()
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
	public void testInvalidFpMemOption()
	{
		String[] args = new String[]{"test.tla", "-fpmem"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fpmem"));
	}
	
	@Test
	public void testNotNumberFpMemOption()
	{
		String[] args = new String[]{"-fpmem", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fpmem"));
	}
	
	@Test
	public void testFpBitsOption()
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
	public void testInvalidFpBitsOption()
	{
		String[] args = new String[]{"test.tla", "-fpbits"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fpbits"));
	}
	
	@Test
	public void testNotNumberFpBitsOption()
	{
		String[] args = new String[]{"-fpbits", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fpbits"));
	}
	
	@Test
	public void testMainSpecOption()
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
	public void testTwoMainSpecs()
	{
		String[] args = new String[]{"first.tla", "second.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.Parse(args);
		assertFalse(result.Success);
	}
	
	/**
	 * Unit tests for CommandLineOptions.Validate function
	 */
	
	@Test
	public void testCoverageIntervalValidation()
	{
		Integer inputValue = 12;
		CommandLineOptions options = new CommandLineOptions();
		options.CoverageIntervalInMinutes = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.Validate(options);
		assertTrue(result.Success);
		assertTrue(result.ErrorMessage.isEmpty());
		
		inputValue = -1;
		options.CoverageIntervalInMinutes = Optional.of(inputValue);
		result = CommandLineOptions.Validate(options);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("coverage"));
	}
	
	@Test
	public void testCheckpointIntervalValidation()
	{
		Integer inputValue = 12;
		CommandLineOptions options = new CommandLineOptions();
		options.CheckpointIntervalInMinutes = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.Validate(options);
		assertTrue(result.Success);
		assertTrue(result.ErrorMessage.isEmpty());
		
		inputValue = -1;
		options.CheckpointIntervalInMinutes = Optional.of(inputValue);
		result = CommandLineOptions.Validate(options);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("checkpoint"));
	}
	
	@Test
	public void testDfidValidation()
	{
		Integer inputValue = 12;
		CommandLineOptions options = new CommandLineOptions();
		options.DfidStartingDepth = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.Validate(options);
		assertTrue(result.Success);
		assertTrue(result.ErrorMessage.isEmpty());
		
		inputValue = -1;
		options.DfidStartingDepth = Optional.of(inputValue);
		result = CommandLineOptions.Validate(options);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("dfid"));
	}
	
	@Test
	public void testFpSetValidation()
	{
		Double inputValue = 0.5;
		CommandLineOptions options = new CommandLineOptions();
		options.FingerprintSetMemoryUsePercentage = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.Validate(options);
		assertTrue(result.Success);
		assertTrue(result.ErrorMessage.isEmpty());
		
		inputValue = -0.5;
		options.FingerprintSetMemoryUsePercentage = Optional.of(inputValue);
		result = CommandLineOptions.Validate(options);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fpset"));
	}
	
	@Test
	public void testMaxSetSizeValidation()
	{
		Integer inputValue = 1;
		CommandLineOptions options = new CommandLineOptions();
		options.MaxSetSize = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.Validate(options);
		assertTrue(result.Success);
		assertTrue(result.ErrorMessage.isEmpty());
		
		inputValue = 0;
		options.MaxSetSize = Optional.of(inputValue);
		result = CommandLineOptions.Validate(options);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("maxSetSize"));
	}
	
	@Test
	public void testFpFunctionIndexValidation()
	{
		Integer inputValue = 0;
		CommandLineOptions options = new CommandLineOptions();
		options.FingerprintFunctionIndex = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.Validate(options);
		assertTrue(result.Success);
		assertTrue(result.ErrorMessage.isEmpty());
		
		inputValue = -1;
		options.FingerprintFunctionIndex = Optional.of(inputValue);
		result = CommandLineOptions.Validate(options);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fp"));

		inputValue = FP64.Polys.length;
		options.FingerprintFunctionIndex = Optional.of(inputValue);
		result = CommandLineOptions.Validate(options);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fp"));
	}
	
	@Test
	public void testFpBitsValidation()
	{
		Integer inputValue = 0;
		CommandLineOptions options = new CommandLineOptions();
		options.FingerprintBits = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.Validate(options);
		assertTrue(result.Success);
		assertTrue(result.ErrorMessage.isEmpty());
		
		inputValue = -1;
		options.FingerprintBits = Optional.of(inputValue);
		result = CommandLineOptions.Validate(options);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fpbits"));

		inputValue = MultiFPSet.MAX_FPBITS + 1;
		options.FingerprintBits = Optional.of(inputValue);
		result = CommandLineOptions.Validate(options);
		assertFalse(result.Success);
		assertTrue(result.ErrorMessage.isPresent());
		assertTrue(result.ErrorMessage.get().contains("fpbits"));
	}
	
	/**
	 * Unit tests for CommandLineOptions.Transform function
	 */
	
	@Test
	public void testLivenessCheckTransform()
	{
		final String inputValue = "SomeStringWithCapitalLetters";
		final String expectedValue = inputValue.toLowerCase();
		CommandLineOptions options = new CommandLineOptions();
		options.LivenessCheck = Optional.of(inputValue);
		CommandLineOptions.Transform(options);
		assertEquals(expectedValue, options.LivenessCheck.get());
	}
	
	@Test
	public void testConfigFileTransform()
	{
		final String expectedValue = "ConfigFile";
		final String inputValue = expectedValue + TLAConstants.Files.CONFIG_EXTENSION;
		CommandLineOptions options = new CommandLineOptions();
		options.ConfigurationFilePath = Optional.of(inputValue);
		CommandLineOptions.Transform(options);
		assertEquals(expectedValue, options.ConfigurationFilePath.get());
		CommandLineOptions.Transform(options);
		assertEquals(expectedValue, options.ConfigurationFilePath.get());
	}
	
	@Test
	public void testDumpFileTransform()
	{
		final String inputValue = "dumpFile";
		String expectedValue = inputValue + ".dump";
		CommandLineOptions options = new CommandLineOptions();
		options.DumpFilePath = Optional.of(inputValue);
		CommandLineOptions.Transform(options);
		assertEquals(expectedValue, options.DumpFilePath.get());
		CommandLineOptions.Transform(options);
		assertEquals(expectedValue, options.DumpFilePath.get());
		
		expectedValue = inputValue + ".dot";
		options = new CommandLineOptions();
		options.DumpFilePath = Optional.of(inputValue);
		options.DumpFileOptions = Optional.of(new CommandLineOptions.DumpFileControls(false, false, false));
		CommandLineOptions.Transform(options);
		assertEquals(expectedValue, options.DumpFilePath.get());
		CommandLineOptions.Transform(options);
		assertEquals(expectedValue, options.DumpFilePath.get());
	}
	
	@Test
	public void testRecoveryIdTransform()
	{		
		final String inputValue = String.format("{0}path{0}to{0}file", FileUtil.separator);
		final String expectedValue = inputValue + FileUtil.separator;
		CommandLineOptions options = new CommandLineOptions();
		options.RecoveryId = Optional.of(inputValue);
		CommandLineOptions.Transform(options);
		assertEquals(expectedValue, options.RecoveryId.get());
	}
	
	@Test
	public void testMetadataPathTransform()
	{
		final String inputValue = String.format("{0}path{0}to{0}file", FileUtil.separator);
		final String expectedValue = inputValue + FileUtil.separator;
		CommandLineOptions options = new CommandLineOptions();
		options.MetadataDirectoryPath = Optional.of(inputValue);
		CommandLineOptions.Transform(options);
		assertEquals(expectedValue, options.MetadataDirectoryPath.get());
	}
	
	@Test
	public void testMainSpecFileTransform()
	{
		final String expectedValue = "Spec";
		final String inputValue = expectedValue + TLAConstants.Files.TLA_EXTENSION;
		CommandLineOptions options = new CommandLineOptions();
		options.MainSpecFilePath = Optional.of(inputValue);
		CommandLineOptions.Transform(options);
		assertEquals(expectedValue, options.MainSpecFilePath.get());
		CommandLineOptions.Transform(options);
		assertEquals(expectedValue, options.MainSpecFilePath.get());
	}
}