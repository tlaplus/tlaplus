package tlc2;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

import tlc2.tool.fp.MultiFPSet;
import tlc2.util.FP64;
import util.FileUtil;
import util.TLAConstants;
import util.Either;

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
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.simulationModeFlag);
					assertTrue(actual.simulationBehaviorCountLimit.isEmpty());
					assertTrue(actual.simulationTraceFile.isEmpty());
					return true;
				}));
	}

	@Test
	public void testSimulateFlagWithBehaviorCountLimit()
	{
		final long expected = 1234;
		String[] args = new String[]{"-simulate", "num=" + expected, "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.simulationModeFlag);
					assertTrue(actual.simulationBehaviorCountLimit.isPresent());
					assertEquals(expected, actual.simulationBehaviorCountLimit.get().longValue());
					assertTrue(actual.simulationTraceFile.isEmpty());
					return true;
				}));
	}
	
	@Test
	public void testSimulateFlagWithTraceFile()
	{
		final String expected = "/path/to/file";
		String[] args = new String[]{"-simulate", "file=" + expected, "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.simulationModeFlag);
					assertTrue(actual.simulationBehaviorCountLimit.isEmpty());
					assertTrue(actual.simulationTraceFile.isPresent());
					assertEquals(expected, actual.simulationTraceFile.get());
					return true;
				}));
	}
	
	@Test
	public void testSimulateFlagWithBehaviorCountLimitAndTraceFile()
	{
		final long expectedLimit = 1234;
		final String expectedPath = "/path/to/file";
		String[] args = new String[]{"-simulate", "file=" + expectedPath + ",num=" + expectedLimit, "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.simulationModeFlag);
					assertTrue(actual.simulationTraceFile.isPresent());
					assertEquals(expectedPath, actual.simulationTraceFile.get());
					assertTrue(actual.simulationBehaviorCountLimit.isPresent());
					assertEquals(expectedLimit, actual.simulationBehaviorCountLimit.get().longValue());
					return true;
				}));
	}

	@Test
	public void testSimulateFlagWithBehaviorCountLimitAndTraceFileReverse()
	{
		final long expectedLimit = 1234;
		final String expectedPath = "/path/to/file";
		String[] args = new String[]{"-simulate", "num=" + expectedLimit + ",file=" + expectedPath, "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.simulationModeFlag);
					assertTrue(actual.simulationTraceFile.isPresent());
					assertEquals(expectedPath, actual.simulationTraceFile.get());
					assertTrue(actual.simulationBehaviorCountLimit.isPresent());
					assertEquals(expectedLimit, actual.simulationBehaviorCountLimit.get().longValue());
					return true;
				}));
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
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.simulationModeFlag);
					assertTrue(actual.simulationBehaviorCountLimit.isEmpty());
					assertTrue(actual.simulationTraceFile.isEmpty());
					return true;
				}));
		
		args = new String[]{"test.tla", "-simulate", "num=" + expectedLimit + ",file=" + expectedPath};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> true,
				helpRequest -> false,
				parseSuccess -> false));
	}

	@Test
	public void testModelCheckFlag()
	{
		String[] args = new String[]{"-modelcheck", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.modelCheckFlag);
					return true;
				}));
	}
	
	@Test
	public void testOnlyPrintStateTraceDiffsFlag()
	{
		String[] args = new String[]{"-difftrace", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.onlyPrintStateTraceDiffsFlag);
					return true;
				}));
	}

	@Test
	public void testDeadlockFlag()
	{
		String[] args = new String[]{"-deadlock", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.doNotCheckDeadlockFlag);
					return true;
				}));
	}
	
	@Test
	public void testCleanStateDirectoryFlag()
	{
		String[] args = new String[]{"-cleanup", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.cleanStatesDirectoryFlag);
					return true;
				}));
	}

	@Test
	public void testNoWarningFlag()
	{
		String[] args = new String[]{"-nowarning", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.doNotPrintWarningsFlag);
					return true;
				}));
	}

	@Test
	public void testGZipFlag()
	{
		String[] args = new String[]{"-gzip", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.useGZipFlag);
					return true;
				}));
	}

	@Test
	public void testTerseOutputFlag()
	{
		String[] args = new String[]{"-terse", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.terseOutputFlag);
					return true;
				}));
	}

	@Test
	public void testContinueAfterInvariantViolationFlag()
	{
		String[] args = new String[]{"-continue", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.continueAfterInvariantViolationFlag);
					return true;
				}));
	}

	@Test
	public void testViewFlag()
	{
		String[] args = new String[]{"-view", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.useViewFlag);
					return true;
				}));
	}

	@Test
	public void testDebugFlag()
	{
		String[] args = new String[]{"-debug", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.debugFlag);
					return true;
				}));
	}

	@Test
	public void testToolOutputFlag()
	{
		String[] args = new String[]{"-tool", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.useToolOutputFormatFlag);
					return true;
				}));
	}

	@Test
	public void testGenerateErrorTraceSpecFlag()
	{
		String[] args = new String[]{"-generateSpecTE", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.generateErrorTraceSpecFlag);
					assertFalse(actual.noMonolithErrorTraceSpecFlag);
					return true;
				}));
	}

	@Test
	public void testGenerateErrorTraceSpecFlagWithNoMonolithValue()
	{
		String[] args = new String[]{"-generateSpecTE", "nomonolith", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.generateErrorTraceSpecFlag);
					assertTrue(actual.noMonolithErrorTraceSpecFlag);
					return true;
				}));
	}

	@Test
	public void testHelpFlag()
	{
		String[] args = new String[]{"-help"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> true,
				parseSuccess -> false));
	}

	@Test
	public void testShortHelpFlag()
	{
		String[] args = new String[]{"-h"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> true,
				parseSuccess -> false));
	}

	@Test
	public void testHelpFlagStopsParsingImmediately()
	{
		String[] args = new String[]{"-h", "NotAnOption", "AlsoNotAnOption"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> true,
				parseSuccess -> false));
	}

	@Test
	public void testLivenessCheckOption()
	{
		final String expectedValue = "final";
		String[] args = new String[]{"-lncheck", expectedValue, "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.livenessCheck.isPresent());
					assertEquals(expectedValue, actual.livenessCheck.get());
					return true;
				}));
	}

	@Test
	public void testInvalidLivenessCheckOption()
	{
		String[] args = new String[]{"test.tla", "-lncheck"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("lncheck"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}

	@Test
	public void testConfigOption()
	{
		final String expectedValue = "configFile.cfg";
		String[] args = new String[]{"-config", expectedValue, "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.configurationFilePath.isPresent());
					assertEquals(expectedValue, actual.configurationFilePath.get());
					return true;
				}));
	}

	@Test
	public void testInvalidConfigOption()
	{
		String[] args = new String[]{"test.tla", "-config"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("config"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testDumpOption()
	{
		final String expectedValue = "dump.out";
		String[] args = new String[]{"-dump", expectedValue, "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.dumpFilePath.isPresent());
					assertEquals(expectedValue, actual.dumpFilePath.get());
					assertTrue(actual.dumpFileOptions.isEmpty());
					return true;
				}));
	}
	
	@Test
	public void testInvalidDumpOption()
	{
		String[] args = new String[]{"test.tla", "-dump"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("dump"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
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

			assertTrue(CommandLineOptions.parse(args).map(
					parseFailure -> false,
					helpRequest -> false,
					parseSuccess -> {
						CommandLineOptions actual = parseSuccess.options;
						assertTrue(actual.mainSpecFilePath.isPresent());
						assertTrue(actual.dumpFilePath.isPresent());
						assertEquals(expectedFileValue, actual.dumpFilePath.get());
						assertTrue(actual.dumpFileOptions.isPresent());

						DumpFileOptions actualControls = actual.dumpFileOptions.get();
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
						
						return true;
					}));
		}
	}
	
	@Test
	public void testCoverageOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-coverage", expectedValue.toString(), "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.coverageIntervalInMinutes.isPresent());
					assertEquals(expectedValue, actual.coverageIntervalInMinutes.get());
					return true;
				}));
	}
	
	@Test
	public void testInvalidCoverageOption()
	{
		String[] args = new String[]{"test.tla", "-coverage"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("coverage"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testNotNumberCoverageOption()
	{
		String[] args = new String[]{"-coverage", "NotANumber", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("coverage"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testCheckpointOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-checkpoint", expectedValue.toString(), "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.checkpointIntervalInMinutes.isPresent());
					assertEquals(expectedValue, actual.checkpointIntervalInMinutes.get());
					return true;
				}));
	}
	
	@Test
	public void testInvalidCheckpointOption()
	{
		String[] args = new String[]{"test.tla", "-checkpoint"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("checkpoint"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testNotNumberCheckpointOption()
	{
		String[] args = new String[]{"-checkpoint", "NotANumber", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("checkpoint"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testDepthOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-depth", expectedValue.toString(), "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.simulationTraceDepthLimit.isPresent());
					assertEquals(expectedValue, actual.simulationTraceDepthLimit.get());
					return true;
				}));
	}
	
	@Test
	public void testInvalidDepthOption()
	{
		String[] args = new String[]{"test.tla", "-depth"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("depth"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testNotNumberDepthOption()
	{
		String[] args = new String[]{"-depth", "NotANumber", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("depth"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testSeedOption()
	{
		final Long expectedValue = 2L;
		String[] args = new String[]{"-seed", expectedValue.toString(), "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.seed.isPresent());
					assertEquals(expectedValue, actual.seed.get());
					return true;
				}));
	}
	
	@Test
	public void testInvalidSeedOption()
	{
		String[] args = new String[]{"test.tla", "-seed"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("seed"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testNotNumberSeedOption()
	{
		String[] args = new String[]{"-seed", "NotANumber", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("seed"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testArilOption()
	{
		final Long expectedValue = 2L;
		String[] args = new String[]{"-aril", expectedValue.toString(), "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.aril.isPresent());
					assertEquals(expectedValue, actual.aril.get());
					return true;
				}));
	}
	
	@Test
	public void testInvalidArilOption()
	{
		String[] args = new String[]{"test.tla", "-aril"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("aril"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testNotNumberArilOption()
	{
		String[] args = new String[]{"-aril", "NotANumber", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("aril"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testMaxSetSizeOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-maxSetSize", expectedValue.toString(), "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.maxSetSize.isPresent());
					assertEquals(expectedValue, actual.maxSetSize.get());
					return true;
				}));
	}
	
	@Test
	public void testInvalidMaxSetSizeOption()
	{
		String[] args = new String[]{"test.tla", "-maxSetSize"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("maxSetSize"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testNotNumberMaxSetSizeOption()
	{
		String[] args = new String[]{"-maxSetSize", "NotANumber", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("maxSetSize"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}

	@Test
	public void testRecoverOption()
	{
		final String expectedValue = "somename";
		String[] args = new String[]{"-recover", expectedValue, "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.recoveryId.isPresent());
					assertEquals(expectedValue, actual.recoveryId.get());
					return true;
				}));
	}

	@Test
	public void testInvalidRecoverOption()
	{
		String[] args = new String[]{"test.tla", "-recover"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("recover"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}

	@Test
	public void testMetadataDirectoryOption()
	{
		final String expectedValue = "somename";
		String[] args = new String[]{"-metadir", expectedValue, "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.metadataDirectoryPath.isPresent());
					assertEquals(expectedValue, actual.metadataDirectoryPath.get());
					return true;
				}));
	}

	@Test
	public void testInvalidMetadataDirectoryOption()
	{
		String[] args = new String[]{"test.tla", "-metadir"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("metadir"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}

	@Test
	public void testUserFileOption()
	{
		final String expectedValue = "somename";
		String[] args = new String[]{"-userFile", expectedValue, "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.userOutputFilePath.isPresent());
					assertEquals(expectedValue, actual.userOutputFilePath.get());
					return true;
				}));
	}

	@Test
	public void testInvalidUserFileOption()
	{
		String[] args = new String[]{"test.tla", "-userFile"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("userFile"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}

	@Test
	public void testAutoWorkersOption()
	{
		final String expectedValue = "auto";
		String[] args = new String[]{"-workers", expectedValue, "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.tlcWorkerThreadOptions.isPresent());
					assertTrue(actual.tlcWorkerThreadOptions.get().map(
							auto -> true,
							manual -> false));
					return true;
				}));
	}

	@Test
	public void testManualAutoWorkersOption()
	{
		final Integer expectedValue = 4;
		String[] args = new String[]{"-workers", expectedValue.toString(), "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.tlcWorkerThreadOptions.isPresent());
					assertTrue(actual.tlcWorkerThreadOptions.get().map(
							auto -> false,
							manual -> {
								assertEquals(expectedValue.intValue(), manual.workerThreadCount);
								return true;
							}));
					return true;
				}));
	}

	@Test
	public void testInvalidWorkersOption()
	{
		String[] args = new String[]{"test.tla", "-workers"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("workers"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}

	@Test
	public void TestNotANumberWorkersOption()
	{
		String[] args = new String[]{"-workers", "NotANumber", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("workers"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testDfidOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-dfid", expectedValue.toString(), "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.dfidStartingDepth.isPresent());
					assertEquals(expectedValue, actual.dfidStartingDepth.get());
					return true;
				}));
	}
	
	@Test
	public void testInvalidDfidOption()
	{
		String[] args = new String[]{"test.tla", "-dfid"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("dfid"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testNotNumberDfidOption()
	{
		String[] args = new String[]{"-dfid", "NotANumber", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("dfid"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testFpOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-fp", expectedValue.toString(), "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.fingerprintFunctionIndex.isPresent());
					assertEquals(expectedValue, actual.fingerprintFunctionIndex.get());
					return true;
				}));
	}
	
	@Test
	public void testInvalidFpOption()
	{
		String[] args = new String[]{"test.tla", "-fp"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("fp"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testNotNumberFpOption()
	{
		String[] args = new String[]{"-fp", "NotANumber", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("fp"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testFpMemOption()
	{
		final Double expectedValue = 1.0;
		String[] args = new String[]{"-fpmem", expectedValue.toString(), "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.fingerprintSetMemoryUsePercentage.isPresent());
					assertEquals(expectedValue, actual.fingerprintSetMemoryUsePercentage.get());
					return true;
				}));
	}
	
	@Test
	public void testInvalidFpMemOption()
	{
		String[] args = new String[]{"test.tla", "-fpmem"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("fpmem"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testNotNumberFpMemOption()
	{
		String[] args = new String[]{"-fpmem", "NotANumber", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("fpmem"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testFpBitsOption()
	{
		final Integer expectedValue = 2;
		String[] args = new String[]{"-fpbits", expectedValue.toString(), "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertTrue(actual.fingerprintBits.isPresent());
					assertEquals(expectedValue, actual.fingerprintBits.get());
					return true;
				}));
	}
	
	@Test
	public void testInvalidFpBitsOption()
	{
		String[] args = new String[]{"test.tla", "-fpbits"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("fpbits"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testNotNumberFpBitsOption()
	{
		String[] args = new String[]{"-fpbits", "NotANumber", "test.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> {
					assertTrue(parseFailure.errorMessage.contains("fpbits"));
					return true;
				},
				helpRequest -> false,
				parseSuccess -> false));
	}
	
	@Test
	public void testMainSpecOption()
	{
		final String expectedValue = "test.tla";
		String[] args = new String[]{expectedValue};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> false,
				helpRequest -> false,
				parseSuccess -> {
					CommandLineOptions actual = parseSuccess.options;
					assertTrue(actual.mainSpecFilePath.isPresent());
					assertEquals(expectedValue, actual.mainSpecFilePath.get());
					return true;
				}));
	}
	
	@Test
	public void testTwoMainSpecs()
	{
		String[] args = new String[]{"first.tla", "second.tla"};
		assertTrue(CommandLineOptions.parse(args).map(
				parseFailure -> true,
				helpRequest -> false,
				parseSuccess -> false));
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
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> false,
				validationSuccess -> true));
		
		inputValue = -1;
		options.coverageIntervalInMinutes = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> {
					assertTrue(validationFailure.errorMessage.contains("coverage"));
					return true;
				},
				validationSuccess -> false));
	}
	
	@Test
	public void testCheckpointIntervalValidation()
	{
		Integer inputValue = 12;
		CommandLineOptions options = new CommandLineOptions();
		options.checkpointIntervalInMinutes = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> false,
				validationSuccess -> true));
		
		inputValue = -1;
		options.checkpointIntervalInMinutes = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> {
					assertTrue(validationFailure.errorMessage.contains("checkpoint"));
					return true;
				},
				validationSuccess -> false));
	}
	
	@Test
	public void testDfidValidation()
	{
		Integer inputValue = 12;
		CommandLineOptions options = new CommandLineOptions();
		options.dfidStartingDepth = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> false,
				validationSuccess -> true));
		
		inputValue = -1;
		options.dfidStartingDepth = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> {
					assertTrue(validationFailure.errorMessage.contains("dfid"));
					return true;
				},
				validationSuccess -> false));
	}
	
	@Test
	public void testFpSetValidation()
	{
		Double inputValue = 0.5;
		CommandLineOptions options = new CommandLineOptions();
		options.fingerprintSetMemoryUsePercentage = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> false,
				validationSuccess -> true));
		
		inputValue = -0.5;
		options.fingerprintSetMemoryUsePercentage = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> {
					assertTrue(validationFailure.errorMessage.contains("fpset"));
					return true;
				},
				validationSuccess -> false));
	}
	
	@Test
	public void testMaxSetSizeValidation()
	{
		Integer inputValue = 1;
		CommandLineOptions options = new CommandLineOptions();
		options.maxSetSize = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> false,
				validationSuccess -> true));
		
		inputValue = 0;
		options.maxSetSize = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> {
					assertTrue(validationFailure.errorMessage.contains("maxSetSize"));
					return true;
				},
				validationSuccess -> false));
	}
	
	@Test
	public void testManualWorkerValidation()
	{
		Integer inputValue = 1;
		CommandLineOptions options = new CommandLineOptions();
		CommandLineOptions.ManuallySetTlcWorkerThreadCount controls =
				new CommandLineOptions.ManuallySetTlcWorkerThreadCount(inputValue);
		options.tlcWorkerThreadOptions = Optional.of(Either.right(controls));
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> false,
				validationSuccess -> true));
		
		inputValue = 0;
		controls = new CommandLineOptions.ManuallySetTlcWorkerThreadCount(inputValue);
		options.tlcWorkerThreadOptions = Optional.of(Either.right(controls));
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> {
					assertTrue(validationFailure.errorMessage.contains("workers"));
					return true;
				},
				validationSuccess -> false));
	}
	
	@Test
	public void TestAutoWorkerValidation()
	{
		final CommandLineOptions options = new CommandLineOptions();
		final CommandLineOptions.AutomaticallySetTlcWorkerThreadCount controls =
				new CommandLineOptions.AutomaticallySetTlcWorkerThreadCount();
		options.tlcWorkerThreadOptions = Optional.of(Either.left(controls));
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> false,
				validationSuccess -> true));
		assertTrue(CommandLineOptions.validate(options, () -> 1).map(
				validationFailure -> false,
				validationSuccess -> true));
		assertTrue(CommandLineOptions.validate(options, () -> 0).map(
				validationFailure -> true,
				validationSuccess -> false));
		assertTrue(CommandLineOptions.validate(options, () -> -1).map(
				validationFailure -> true,
				validationSuccess -> false));
	}
	
	@Test
	public void testFpFunctionIndexValidation()
	{
		Integer inputValue = 0;
		CommandLineOptions options = new CommandLineOptions();
		options.fingerprintFunctionIndex = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> false,
				validationSuccess -> true));
		
		inputValue = -1;
		options.fingerprintFunctionIndex = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> {
					assertTrue(validationFailure.errorMessage.contains("fp"));
					return true;
				},
				validationSuccess -> false));

		inputValue = FP64.Polys.length;
		options.fingerprintFunctionIndex = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> {
					assertTrue(validationFailure.errorMessage.contains("fp"));
					return true;
				},
				validationSuccess -> false));
	}
	
	@Test
	public void testFpBitsValidation()
	{
		Integer inputValue = 0;
		CommandLineOptions options = new CommandLineOptions();
		options.fingerprintBits = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> false,
				validationSuccess -> true));
		
		inputValue = -1;
		options.fingerprintBits = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> {
					assertTrue(validationFailure.errorMessage.contains("fpbits"));
					return true;
				},
				validationSuccess -> false));

		inputValue = MultiFPSet.MAX_FPBITS + 1;
		options.fingerprintBits = Optional.of(inputValue);
		assertTrue(CommandLineOptions.validate(options, () -> 4).map(
				validationFailure -> {
					assertTrue(validationFailure.errorMessage.contains("fpbits"));
					return true;
				},
				validationSuccess -> false));
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
		options.transform();
		assertEquals(expectedValue, options.livenessCheck.get());
	}
	
	@Test
	public void testConfigFileTransform()
	{
		final String expectedValue = "ConfigFile";
		final String inputValue = expectedValue + TLAConstants.Files.CONFIG_EXTENSION;
		CommandLineOptions options = new CommandLineOptions();
		options.configurationFilePath = Optional.of(inputValue);
		options.transform();
		assertEquals(expectedValue, options.configurationFilePath.get());
		options.transform();
		assertEquals(expectedValue, options.configurationFilePath.get());
	}
	
	@Test
	public void testDumpFileTransform()
	{
		final String inputValue = "dumpFile";
		String expectedValue = inputValue + ".dump";
		CommandLineOptions options = new CommandLineOptions();
		options.dumpFilePath = Optional.of(inputValue);
		options.transform();
		assertEquals(expectedValue, options.dumpFilePath.get());
		options.transform();
		assertEquals(expectedValue, options.dumpFilePath.get());
		
		expectedValue = inputValue + ".dot";
		options = new CommandLineOptions();
		options.dumpFilePath = Optional.of(inputValue);
		options.dumpFileOptions = Optional.of(new DumpFileOptions(false, false, false));
		options.transform();
		assertEquals(expectedValue, options.dumpFilePath.get());
		options.transform();
		assertEquals(expectedValue, options.dumpFilePath.get());
	}
	
	@Test
	public void testRecoveryIdTransform()
	{		
		final String inputValue = String.format("{0}path{0}to{0}file", FileUtil.separator);
		final String expectedValue = inputValue + FileUtil.separator;
		CommandLineOptions options = new CommandLineOptions();
		options.recoveryId = Optional.of(inputValue);
		options.transform();
		assertEquals(expectedValue, options.recoveryId.get());
	}
	
	@Test
	public void testMetadataPathTransform()
	{
		final String inputValue = String.format("{0}path{0}to{0}file", FileUtil.separator);
		final String expectedValue = inputValue + FileUtil.separator;
		CommandLineOptions options = new CommandLineOptions();
		options.metadataDirectoryPath = Optional.of(inputValue);
		options.transform();
		assertEquals(expectedValue, options.metadataDirectoryPath.get());
	}
	
	@Test
	public void testMainSpecFileTransform()
	{
		final String expectedValue = "Spec";
		final String inputValue = expectedValue + TLAConstants.Files.TLA_EXTENSION;
		CommandLineOptions options = new CommandLineOptions();
		options.mainSpecFilePath = Optional.of(inputValue);
		options.transform();
		assertEquals(expectedValue, options.mainSpecFilePath.get());
		options.transform();
		assertEquals(expectedValue, options.mainSpecFilePath.get());
	}
}