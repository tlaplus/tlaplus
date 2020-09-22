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

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.simulationModeFlag);
		assertTrue(actual.simulationBehaviorCountLimit.isEmpty());
		assertTrue(actual.simulationTraceFile.isEmpty());
	}

	@Test
	public void testSimulateFlagWithBehaviorCountLimit()
	{
		final long expected = 1234;
		String[] args = new String[]{"-simulate", "num=" + expected, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();
		
		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.simulationModeFlag);
		assertTrue(actual.simulationTraceFile.isEmpty());
		assertTrue(actual.simulationBehaviorCountLimit.isPresent());
		assertEquals(expected, actual.simulationBehaviorCountLimit.get().longValue());
	}
	
	@Test
	public void testSimulateFlagWithTraceFile()
	{
		final String expected = "/path/to/file";
		String[] args = new String[]{"-simulate", "file=" + expected, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();
		
		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.simulationModeFlag);
		assertTrue(actual.simulationBehaviorCountLimit.isEmpty());
		assertTrue(actual.simulationTraceFile.isPresent());
		assertEquals(expected, actual.simulationTraceFile.get());
	}
	
	@Test
	public void testSimulateFlagWithBehaviorCountLimitAndTraceFile()
	{
		final long expectedLimit = 1234;
		final String expectedPath = "/path/to/file";
		String[] args = new String[]{"-simulate", "file=" + expectedPath + ",num=" + expectedLimit, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();
		
		assertTrue(actual.simulationModeFlag);
		assertTrue(actual.simulationTraceFile.isPresent());
		assertEquals(expectedPath, actual.simulationTraceFile.get());

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.simulationModeFlag);
		assertTrue(actual.simulationBehaviorCountLimit.isPresent());
		assertEquals(expectedLimit, actual.simulationBehaviorCountLimit.get().longValue());
	}

	@Test
	public void testSimulateFlagWithBehaviorCountLimitAndTraceFileReverse()
	{
		final long expectedLimit = 1234;
		final String expectedPath = "/path/to/file";
		String[] args = new String[]{"-simulate", "num=" + expectedLimit + ",file=" + expectedPath, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();
		
		assertTrue(actual.simulationModeFlag);
		assertTrue(actual.simulationTraceFile.isPresent());
		assertEquals(expectedPath, actual.simulationTraceFile.get());

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.simulationModeFlag);
		assertTrue(actual.simulationBehaviorCountLimit.isPresent());
		assertEquals(expectedLimit, actual.simulationBehaviorCountLimit.get().longValue());
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

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.simulationModeFlag);
		assertTrue(actual.simulationBehaviorCountLimit.isEmpty());
		assertTrue(actual.simulationTraceFile.isEmpty());
		assertTrue(actual.mainSpecFilePath.isPresent());
		
		args = new String[]{"test.tla", "-simulate", "num=" + expectedLimit + ",file=" + expectedPath};
		result = CommandLineOptions.parse(args);
		assertFalse(result.success);
	}

	@Test
	public void testModelCheckFlag()
	{
		String[] args = new String[]{"-modelcheck", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.modelCheckFlag);
	}
	
	@Test
	public void testOnlyPrintStateTraceDiffsFlag()
	{
		String[] args = new String[]{"-difftrace", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.onlyPrintStateTraceDiffsFlag);
	}

	@Test
	public void testDeadlockFlag()
	{
		String[] args = new String[]{"-deadlock", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.doNotCheckDeadlockFlag);
	}
	
	@Test
	public void testCleanStateDirectoryFlag()
	{
		String[] args = new String[]{"-cleanup", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.cleanStatesDirectoryFlag);
	}

	@Test
	public void testNoWarningFlag()
	{
		String[] args = new String[]{"-nowarning", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.doNotPrintWarningsFlag);
	}

	@Test
	public void testGZipFlag()
	{
		String[] args = new String[]{"-gzip", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.useGZipFlag);
	}

	@Test
	public void testTerseOutputFlag()
	{
		String[] args = new String[]{"-terse", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.terseOutputFlag);
	}

	@Test
	public void testContinueAfterInvariantViolationFlag()
	{
		String[] args = new String[]{"-continue", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.continueAfterInvariantViolationFlag);
	}

	@Test
	public void testViewFlag()
	{
		String[] args = new String[]{"-view", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.useViewFlag);
	}

	@Test
	public void testDebugFlag()
	{
		String[] args = new String[]{"-debug", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.debugFlag);
	}

	@Test
	public void testToolOutputFlag()
	{
		String[] args = new String[]{"-tool", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.useToolOutputFormatFlag);
	}

	@Test
	public void testGenerateErrorTraceSpecFlag()
	{
		String[] args = new String[]{"-generateSpecTE", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.generateErrorTraceSpecFlag);
		assertFalse(actual.noMonolithErrorTraceSpecFlag);
	}

	@Test
	public void testGenerateErrorTraceSpecFlagWithNoMonolithValue()
	{
		String[] args = new String[]{"-generateSpecTE", "nomonolith", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.generateErrorTraceSpecFlag);
		assertTrue(actual.noMonolithErrorTraceSpecFlag);
	}

	@Test
	public void testHelpFlag()
	{
		String[] args = new String[]{"-help"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.helpRequest);
		assertTrue(result.options.isEmpty());
	}

	@Test
	public void testShortHelpFlag()
	{
		String[] args = new String[]{"-h"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.helpRequest);
		assertTrue(result.options.isEmpty());
	}

	@Test
	public void testHelpFlagWithGibberish()
	{
		String[] args = new String[]{"-h", "NotAnOption", "AlsoNotAnOption"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.helpRequest);
		assertTrue(result.options.isEmpty());
	}

	@Test
	public void testLivenessCheckOption()
	{
		final String expectedValue = "final";
		String[] args = new String[]{"-lncheck", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.livenessCheck.isPresent());
		assertEquals(expectedValue, actual.livenessCheck.get());
	}

	@Test
	public void testInvalidLivenessCheckOption()
	{
		String[] args = new String[]{"test.tla", "-lncheck"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("lncheck"));
	}

	@Test
	public void testConfigOption()
	{
		final String expectedValue = "configFile.cfg";
		String[] args = new String[]{"-config", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.configurationFilePath.isPresent());
		assertEquals(expectedValue, actual.configurationFilePath.get());
	}

	@Test
	public void testInvalidConfigOption()
	{
		String[] args = new String[]{"test.tla", "-config"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("config"));
	}
	
	@Test
	public void testDumpOption()
	{
		final String expectedValue = "dump.out";
		String[] args = new String[]{"-dump", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.dumpFilePath.isPresent());
		assertEquals(expectedValue, actual.dumpFilePath.get());
		assertTrue(actual.dumpFileOptions.isEmpty());
	}
	
	@Test
	public void testInvalidDumpOption()
	{
		String[] args = new String[]{"test.tla", "-dump"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("dump"));
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

			CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
			assertTrue(result.success);
			assertTrue(result.options.isPresent());
			CommandLineOptions actual = result.options.get();

			assertTrue(actual.mainSpecFilePath.isPresent());
			assertTrue(actual.dumpFilePath.isPresent());
			assertEquals(expectedFileValue, actual.dumpFilePath.get());
			assertTrue(actual.dumpFileOptions.isPresent());
			CommandLineOptions.DumpFileControls actualControls = actual.dumpFileOptions.get();
			
			if (flagList.contains("colorize"))
			{
				assertTrue(actualControls.colorize);
			}
			
			if (flagList.contains("actionlabels"))
			{
				assertTrue(actualControls.actionLabels);
			}
			
			if (flagList.contains("snapshot"))
			{
				assertTrue(actualControls.snapshot);
			}
		}
	}
	
	@Test
	public void testCoverageOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-coverage", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.coverageIntervalInMinutes.isPresent());
		assertEquals(expectedValue, actual.coverageIntervalInMinutes.get());
	}
	
	@Test
	public void testInvalidCoverageOption()
	{
		String[] args = new String[]{"test.tla", "-coverage"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("coverage"));
	}
	
	@Test
	public void testNotNumberCoverageOption()
	{
		String[] args = new String[]{"-coverage", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("coverage"));
	}
	
	@Test
	public void testCheckpointOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-checkpoint", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.checkpointIntervalInMinutes.isPresent());
		assertEquals(expectedValue, actual.checkpointIntervalInMinutes.get());
	}
	
	@Test
	public void testInvalidCheckpointOption()
	{
		String[] args = new String[]{"test.tla", "-checkpoint"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("checkpoint"));
	}
	
	@Test
	public void testNotNumberCheckpointOption()
	{
		String[] args = new String[]{"-checkpoint", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("checkpoint"));
	}
	
	@Test
	public void testDepthOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-depth", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.simulationTraceDepthLimit.isPresent());
		assertEquals(expectedValue, actual.simulationTraceDepthLimit.get());
	}
	
	@Test
	public void testInvalidDepthOption()
	{
		String[] args = new String[]{"test.tla", "-depth"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("depth"));
	}
	
	@Test
	public void testNotNumberDepthOption()
	{
		String[] args = new String[]{"-depth", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("depth"));
	}
	
	@Test
	public void testSeedOption()
	{
		final Long expectedValue = 2L;
		String[] args = new String[]{"-seed", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.seed.isPresent());
		assertEquals(expectedValue, actual.seed.get());
	}
	
	@Test
	public void testInvalidSeedOption()
	{
		String[] args = new String[]{"test.tla", "-seed"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("seed"));
	}
	
	@Test
	public void testNotNumberSeedOption()
	{
		String[] args = new String[]{"-seed", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("seed"));
	}
	
	@Test
	public void testArilOption()
	{
		final Long expectedValue = 2L;
		String[] args = new String[]{"-aril", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.aril.isPresent());
		assertEquals(expectedValue, actual.aril.get());
	}
	
	@Test
	public void testInvalidArilOption()
	{
		String[] args = new String[]{"test.tla", "-aril"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("aril"));
	}
	
	@Test
	public void testNotNumberArilOption()
	{
		String[] args = new String[]{"-aril", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("aril"));
	}
	
	@Test
	public void testMaxSetSizeOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-maxSetSize", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.maxSetSize.isPresent());
		assertEquals(expectedValue, actual.maxSetSize.get());
	}
	
	@Test
	public void testInvalidMaxSetSizeOption()
	{
		String[] args = new String[]{"test.tla", "-maxSetSize"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("maxSetSize"));
	}
	
	@Test
	public void testNotNumberMaxSetSizeOption()
	{
		String[] args = new String[]{"-maxSetSize", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("maxSetSize"));
	}

	@Test
	public void testRecoverOption()
	{
		final String expectedValue = "somename";
		String[] args = new String[]{"-recover", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.recoveryId.isPresent());
		assertEquals(expectedValue, actual.recoveryId.get());
	}

	@Test
	public void testInvalidRecoverOption()
	{
		String[] args = new String[]{"test.tla", "-recover"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("recover"));
	}

	@Test
	public void testMetadataDirectoryOption()
	{
		final String expectedValue = "somename";
		String[] args = new String[]{"-metadir", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.metadataDirectoryPath.isPresent());
		assertEquals(expectedValue, actual.metadataDirectoryPath.get());
	}

	@Test
	public void testInvalidMetadataDirectoryOption()
	{
		String[] args = new String[]{"test.tla", "-metadir"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("metadir"));
	}

	@Test
	public void testUserFileOption()
	{
		final String expectedValue = "somename";
		String[] args = new String[]{"-userFile", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.userOutputFilePath.isPresent());
		assertEquals(expectedValue, actual.userOutputFilePath.get());
	}

	@Test
	public void testInvalidUserFileOption()
	{
		String[] args = new String[]{"test.tla", "-userFile"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("userFile"));
	}

	@Test
	public void testAutoWorkersOption()
	{
		final String expectedValue = "auto";
		String[] args = new String[]{"-workers", expectedValue, "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.tlcWorkerThreadOptions.isPresent());
		assertTrue(actual.tlcWorkerThreadOptions.get().automatic);
		assertTrue(actual.tlcWorkerThreadOptions.get().threadCount.isEmpty());
	}

	@Test
	public void testManualAutoWorkersOption()
	{
		final Integer expectedValue = 4;
		String[] args = new String[]{"-workers", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.tlcWorkerThreadOptions.isPresent());
		assertFalse(actual.tlcWorkerThreadOptions.get().automatic);
		assertTrue(actual.tlcWorkerThreadOptions.get().threadCount.isPresent());
		assertEquals(expectedValue, actual.tlcWorkerThreadOptions.get().threadCount.get());
	}

	@Test
	public void testInvalidWorkersOption()
	{
		String[] args = new String[]{"test.tla", "-workers"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("workers"));
	}

	@Test
	public void TestNotANumberWorkersOption()
	{
		String[] args = new String[]{"-workers", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("workers"));
	}
	
	@Test
	public void testDfidOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-dfid", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.dfidStartingDepth.isPresent());
		assertEquals(expectedValue, actual.dfidStartingDepth.get());
	}
	
	@Test
	public void testInvalidDfidOption()
	{
		String[] args = new String[]{"test.tla", "-dfid"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("dfid"));
	}
	
	@Test
	public void testNotNumberDfidOption()
	{
		String[] args = new String[]{"-dfid", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("dfid"));
	}
	
	@Test
	public void testFpOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-fp", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.fingerprintFunctionIndex.isPresent());
		assertEquals(expectedValue, actual.fingerprintFunctionIndex.get());
	}
	
	@Test
	public void testInvalidFpOption()
	{
		String[] args = new String[]{"test.tla", "-fp"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("fp"));
	}
	
	@Test
	public void testNotNumberFpOption()
	{
		String[] args = new String[]{"-fp", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("fp"));
	}
	
	@Test
	public void testFpMemOption()
	{
		final Double expectedValue = 1.0;
		String[] args = new String[]{"-fpmem", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.fingerprintSetMemoryUsePercentage.isPresent());
		assertEquals(expectedValue, actual.fingerprintSetMemoryUsePercentage.get());
	}
	
	@Test
	public void testInvalidFpMemOption()
	{
		String[] args = new String[]{"test.tla", "-fpmem"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("fpmem"));
	}
	
	@Test
	public void testNotNumberFpMemOption()
	{
		String[] args = new String[]{"-fpmem", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("fpmem"));
	}
	
	@Test
	public void testFpBitsOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-fpbits", expectedValue.toString(), "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertTrue(actual.fingerprintBits.isPresent());
		assertEquals(expectedValue, actual.fingerprintBits.get());
	}
	
	@Test
	public void testInvalidFpBitsOption()
	{
		String[] args = new String[]{"test.tla", "-fpbits"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("fpbits"));
	}
	
	@Test
	public void testNotNumberFpBitsOption()
	{
		String[] args = new String[]{"-fpbits", "NotANumber", "test.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("fpbits"));
	}
	
	@Test
	public void testMainSpecOption()
	{
		final String expectedValue = "test.tla";
		String[] args = new String[]{expectedValue};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertTrue(result.success);
		assertTrue(result.options.isPresent());
		CommandLineOptions actual = result.options.get();

		assertTrue(actual.mainSpecFilePath.isPresent());
		assertEquals(expectedValue, actual.mainSpecFilePath.get());
	}
	
	@Test
	public void testTwoMainSpecs()
	{
		String[] args = new String[]{"first.tla", "second.tla"};

		CommandLineOptions.ParseResult result = CommandLineOptions.parse(args);
		assertFalse(result.success);
	}
	
	/**
	 * Unit tests for CommandLineOptions.Validate function
	 */
	
	@Test
	public void testCoverageIntervalValidation()
	{
		Integer inputValue = 12;
		CommandLineOptions options = new CommandLineOptions();
		options.coverageIntervalInMinutes = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.validate(options);
		assertTrue(result.success);
		assertTrue(result.errorMessage.isEmpty());
		
		inputValue = -1;
		options.coverageIntervalInMinutes = Optional.of(inputValue);
		result = CommandLineOptions.validate(options);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("coverage"));
	}
	
	@Test
	public void testCheckpointIntervalValidation()
	{
		Integer inputValue = 12;
		CommandLineOptions options = new CommandLineOptions();
		options.checkpointIntervalInMinutes = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.validate(options);
		assertTrue(result.success);
		assertTrue(result.errorMessage.isEmpty());
		
		inputValue = -1;
		options.checkpointIntervalInMinutes = Optional.of(inputValue);
		result = CommandLineOptions.validate(options);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("checkpoint"));
	}
	
	@Test
	public void testDfidValidation()
	{
		Integer inputValue = 12;
		CommandLineOptions options = new CommandLineOptions();
		options.dfidStartingDepth = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.validate(options);
		assertTrue(result.success);
		assertTrue(result.errorMessage.isEmpty());
		
		inputValue = -1;
		options.dfidStartingDepth = Optional.of(inputValue);
		result = CommandLineOptions.validate(options);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("dfid"));
	}
	
	@Test
	public void testFpSetValidation()
	{
		Double inputValue = 0.5;
		CommandLineOptions options = new CommandLineOptions();
		options.fingerprintSetMemoryUsePercentage = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.validate(options);
		assertTrue(result.success);
		assertTrue(result.errorMessage.isEmpty());
		
		inputValue = -0.5;
		options.fingerprintSetMemoryUsePercentage = Optional.of(inputValue);
		result = CommandLineOptions.validate(options);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("fpset"));
	}
	
	@Test
	public void testMaxSetSizeValidation()
	{
		Integer inputValue = 1;
		CommandLineOptions options = new CommandLineOptions();
		options.maxSetSize = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.validate(options);
		assertTrue(result.success);
		assertTrue(result.errorMessage.isEmpty());
		
		inputValue = 0;
		options.maxSetSize = Optional.of(inputValue);
		result = CommandLineOptions.validate(options);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("maxSetSize"));
	}
	
	@Test
	public void testFpFunctionIndexValidation()
	{
		Integer inputValue = 0;
		CommandLineOptions options = new CommandLineOptions();
		options.fingerprintFunctionIndex = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.validate(options);
		assertTrue(result.success);
		assertTrue(result.errorMessage.isEmpty());
		
		inputValue = -1;
		options.fingerprintFunctionIndex = Optional.of(inputValue);
		result = CommandLineOptions.validate(options);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("fp"));

		inputValue = FP64.Polys.length;
		options.fingerprintFunctionIndex = Optional.of(inputValue);
		result = CommandLineOptions.validate(options);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("fp"));
	}
	
	@Test
	public void testFpBitsValidation()
	{
		Integer inputValue = 0;
		CommandLineOptions options = new CommandLineOptions();
		options.fingerprintBits = Optional.of(inputValue);
		CommandLineOptions.ValidationResult result = CommandLineOptions.validate(options);
		assertTrue(result.success);
		assertTrue(result.errorMessage.isEmpty());
		
		inputValue = -1;
		options.fingerprintBits = Optional.of(inputValue);
		result = CommandLineOptions.validate(options);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("fpbits"));

		inputValue = MultiFPSet.MAX_FPBITS + 1;
		options.fingerprintBits = Optional.of(inputValue);
		result = CommandLineOptions.validate(options);
		assertFalse(result.success);
		assertTrue(result.errorMessage.isPresent());
		assertTrue(result.errorMessage.get().contains("fpbits"));
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
		options.livenessCheck = Optional.of(inputValue);
		CommandLineOptions.transform(options);
		assertEquals(expectedValue, options.livenessCheck.get());
	}
	
	@Test
	public void testConfigFileTransform()
	{
		final String expectedValue = "ConfigFile";
		final String inputValue = expectedValue + TLAConstants.Files.CONFIG_EXTENSION;
		CommandLineOptions options = new CommandLineOptions();
		options.configurationFilePath = Optional.of(inputValue);
		CommandLineOptions.transform(options);
		assertEquals(expectedValue, options.configurationFilePath.get());
		CommandLineOptions.transform(options);
		assertEquals(expectedValue, options.configurationFilePath.get());
	}
	
	@Test
	public void testDumpFileTransform()
	{
		final String inputValue = "dumpFile";
		String expectedValue = inputValue + ".dump";
		CommandLineOptions options = new CommandLineOptions();
		options.dumpFilePath = Optional.of(inputValue);
		CommandLineOptions.transform(options);
		assertEquals(expectedValue, options.dumpFilePath.get());
		CommandLineOptions.transform(options);
		assertEquals(expectedValue, options.dumpFilePath.get());
		
		expectedValue = inputValue + ".dot";
		options = new CommandLineOptions();
		options.dumpFilePath = Optional.of(inputValue);
		options.dumpFileOptions = Optional.of(new CommandLineOptions.DumpFileControls(false, false, false));
		CommandLineOptions.transform(options);
		assertEquals(expectedValue, options.dumpFilePath.get());
		CommandLineOptions.transform(options);
		assertEquals(expectedValue, options.dumpFilePath.get());
	}
	
	@Test
	public void testRecoveryIdTransform()
	{		
		final String inputValue = String.format("{0}path{0}to{0}file", FileUtil.separator);
		final String expectedValue = inputValue + FileUtil.separator;
		CommandLineOptions options = new CommandLineOptions();
		options.recoveryId = Optional.of(inputValue);
		CommandLineOptions.transform(options);
		assertEquals(expectedValue, options.recoveryId.get());
	}
	
	@Test
	public void testMetadataPathTransform()
	{
		final String inputValue = String.format("{0}path{0}to{0}file", FileUtil.separator);
		final String expectedValue = inputValue + FileUtil.separator;
		CommandLineOptions options = new CommandLineOptions();
		options.metadataDirectoryPath = Optional.of(inputValue);
		CommandLineOptions.transform(options);
		assertEquals(expectedValue, options.metadataDirectoryPath.get());
	}
	
	@Test
	public void testMainSpecFileTransform()
	{
		final String expectedValue = "Spec";
		final String inputValue = expectedValue + TLAConstants.Files.TLA_EXTENSION;
		CommandLineOptions options = new CommandLineOptions();
		options.mainSpecFilePath = Optional.of(inputValue);
		CommandLineOptions.transform(options);
		assertEquals(expectedValue, options.mainSpecFilePath.get());
		CommandLineOptions.transform(options);
		assertEquals(expectedValue, options.mainSpecFilePath.get());
	}
}