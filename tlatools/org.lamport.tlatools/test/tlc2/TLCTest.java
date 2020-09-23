package tlc2;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assume.assumeTrue;

import java.util.ArrayList;
import java.util.function.Supplier;

import org.junit.Test;

import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.FPSetFactory;
import tlc2.tool.fp.MultiFPSet;
import tlc2.util.FP64;
import util.FileUtil;
import util.TLAConstants;
import util.TLCRuntime;

public class TLCTest {

	@Test
	public void testHandleParametersAbsoluteInvalid() {
		final TLC tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-fpmem", "-1", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME}));
	}
	
	@Test
	public void testHandleParametersAbsoluteValid() {
		final TLC tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-fpmem", "101", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME}));
	}
	
	@Test
	public void testHandleParametersFractionInvalid() {
		final TLC tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-fpmem", "-0.5", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME}));
	}
	
	/**
	 * Allocating to little should result in min default
	 */
	@Test
	public void testHandleParametersAllocateLowerBound() {
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-fpmem", "0", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME};
		assertTrue(tlc.handleParameters(args));
		final FPSetConfiguration fpSetConfiguration = tlc.getFPSetConfiguration();
		assumeTrue(FPSetFactory.allocatesOnHeap(fpSetConfiguration.getImplementation()));
		assertEquals("Allocating to little should result in min default",
				TLCRuntime.MinFpMemSize, fpSetConfiguration
						.getMemoryInBytes());
	}
	
	/**
	 * Over-allocating should result in max default
	 */
	@Test
	public void testHandleParametersAllocateUpperBound() {
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-fpmem", Long.toString(Long.MAX_VALUE), TLAConstants.Files.MODEL_CHECK_FILE_BASENAME};
		assertTrue(tlc.handleParameters(args));
        final long maxMemory = (long) (Runtime.getRuntime().maxMemory() * 0.75d);
        final FPSetConfiguration fpSetConfiguration = tlc.getFPSetConfiguration();
		assumeTrue(FPSetFactory.allocatesOnHeap(fpSetConfiguration.getImplementation()));
		assertEquals("Overallocating should result in max default (75%)",
				maxMemory, fpSetConfiguration.getMemoryInBytes());
	}
	
	/**
	 * .5 is valid
	 */
	@Test
	public void testHandleParametersAllocateHalf() {
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-fpmem", ".5", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME};
		assertTrue(tlc.handleParameters(args));
        final long maxMemory = (long) (Runtime.getRuntime().maxMemory() * 0.50d);
        final FPSetConfiguration fpSetConfiguration = tlc.getFPSetConfiguration();
		assumeTrue(FPSetFactory.allocatesOnHeap(fpSetConfiguration.getImplementation()));
		assertEquals("Overallocating should result in max default (50%)",
				maxMemory, fpSetConfiguration.getMemoryInBytes());
	}
	
	/**
	 * .99 is valid
	 */
	@Test
	public void testHandleParametersAllocate90() {
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-fpmem", ".99", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME};
		assertTrue(tlc.handleParameters(args));
        final long maxMemory = (long) (Runtime.getRuntime().maxMemory() * 0.99d);
		final FPSetConfiguration fpSetConfiguration = tlc.getFPSetConfiguration();
		assumeTrue(FPSetFactory.allocatesOnHeap(fpSetConfiguration.getImplementation()));
		assertEquals("Overallocating should result in max default (99%)",
				maxMemory, fpSetConfiguration.getMemoryInBytes());
	}
	
	/**
	 *  is valid
	 */
	@Test
	public void testHandleParametersMaxSetSize() {
		final int progDefault = TLCGlobals.setBound;
		
		TLC tlc = new TLC();
		String[] args = new String[] {"-maxSetSize", "NaN", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME};
		assertFalse(tlc.handleParameters(args));
		
		tlc = new TLC();
		args = new String[] {"-maxSetSize", "0", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME};
		assertFalse(tlc.handleParameters(args));

		tlc = new TLC();
		args = new String[] {"-maxSetSize", "-1", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME};
		assertFalse(tlc.handleParameters(args));

		tlc = new TLC();
		args = new String[] { "-maxSetSize", Integer.toString(Integer.MIN_VALUE), TLAConstants.Files.MODEL_CHECK_FILE_BASENAME };
		assertFalse(tlc.handleParameters(args));
				
		tlc = new TLC();
		args = new String[] {"-maxSetSize", "1", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME};
		assertTrue(tlc.handleParameters(args));
		assertEquals(1, TLCGlobals.setBound);
		
		tlc = new TLC();
		args = new String[] { "-maxSetSize", Integer.toString(progDefault), TLAConstants.Files.MODEL_CHECK_FILE_BASENAME };
		assertTrue(tlc.handleParameters(args));
		assertEquals(progDefault, TLCGlobals.setBound);
		
		tlc = new TLC();
		args = new String[] { "-maxSetSize", Integer.toString(Integer.MAX_VALUE), TLAConstants.Files.MODEL_CHECK_FILE_BASENAME};
		assertTrue(tlc.handleParameters(args));
		assertEquals(Integer.MAX_VALUE, TLCGlobals.setBound);
	}
	
	@Test
	public void testRuntimeConversion() {
		assertEquals("59s", TLC.convertRuntimeToHumanReadable(59000L));
		assertEquals("59min 59s", TLC.convertRuntimeToHumanReadable(3599000L));
		assertEquals("23h 59min", TLC.convertRuntimeToHumanReadable(86340000L));
		assertEquals("1d 23h", TLC.convertRuntimeToHumanReadable(169200000L));
		assertEquals("2d 23h", TLC.convertRuntimeToHumanReadable(255600000L));
		assertEquals("99d 23h", TLC.convertRuntimeToHumanReadable(8636400000L));
	}
	
	@Test
	public void testSimulateFlagSetsRunMode()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-simulate", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(TLC.RunMode.SIMULATE, tlc.getRunMode());
	}
	
	@Test
	public void testSimulateFlagWithOptionsSetsVariables()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final long expectedLimit = 1234;
		final String expectedPath = "/path/to/file";
		final String[] args = new String[]{"-simulate", "file=" + expectedPath + ",num=" + expectedLimit, tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(TLC.RunMode.SIMULATE, tlc.getRunMode());
		assertEquals(expectedLimit, tlc.getSimulationBehaviorCountLimit());
		assertEquals(expectedPath, tlc.getTraceFilePath());
	}
	
	@Test
	public void testDiffTraceOptionSetsGlobalVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-difftrace", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertTrue(TLCGlobals.printDiffsOnly);
	}
	
	@Test
	public void testDeadlockOptionSetsVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-deadlock", tlaFile};
		assertTrue(tlc.isDeadlockCheckingEnabled());
		assertTrue(tlc.handleParameters(args));
		assertFalse(tlc.isDeadlockCheckingEnabled());
	}
	
	@Test
	public void testCleanupOptionSetsVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-cleanup", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertTrue(tlc.isStatesDirectoryMarkedForCleanup());
	}
	
	@Test
	public void testWarningOptionSetsGlobalVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-nowarning", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertFalse(TLCGlobals.warn);
	}
	
	@Test
	public void testGZipOptionSetsGlobalVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-gzip", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertTrue(TLCGlobals.useGZIP);
	}
	
	@Test
	public void testTerseOptionSetsGlobalVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-terse", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertFalse(TLCGlobals.expand);
	}
	
	@Test
	public void testContinueOptionSetsGlobalVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-continue", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertTrue(TLCGlobals.continuation);
	}
	
	@Test
	public void testViewOptionSetsGlobalVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-view", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertTrue(TLCGlobals.useView);
	}
	
	@Test
	public void testDebugOptionSetsGlobalVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-debug", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertTrue(TLCGlobals.debug);
	}
	
	@Test
	public void testToolOptionSetsGlobalVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-tool", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertTrue(TLCGlobals.tool);
	}
	
	@Test
	public void testGenerateSpecTeOptionSetsGlobalVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-generateSpecTE", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertTrue(TLCGlobals.tool);
		assertTrue(tlc.willGenerateErrorTraceSpec());
	}
	
	@Test
	public void testLnCheckOptionSetsGlobalVariable()
	{
		final String inputValue = "someTestValue";
		final String expectedValue = inputValue.toLowerCase();
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-lncheck", inputValue, tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertFalse(inputValue.equals(TLCGlobals.lnCheck));
		assertEquals(expectedValue, TLCGlobals.lnCheck);
	}
	
	@Test
	public void testConfigOptionSetsVariable()
	{
		final String expected = "test.config";
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-config", expected, tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expected, tlc.getConfigFile());
	}
	
	@Test
	public void testDumpOptionSetsVariable()
	{
		final String input = "test";
		final String expected = input + ".dump";
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-dump", expected, tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expected, tlc.getDumpFile());
	}
	
	@Test
	public void testMultipleDumpOptionsSetVariables()
	{
		final String[] possibleFlags = new String[]{"colorize", "actionlabels", "snapshot"};
		final String inputFileValue = "dump";
		final String expectedFileValue = inputFileValue + ".dot";
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		
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
			final String[] args = new String[]{"-dump", flags, inputFileValue, tlaFile};
			final TLC tlc = new TLC();
			assertTrue(tlc.handleParameters(args));
			assertEquals(expectedFileValue, tlc.getDumpFile());
			DumpFileOptions actual = tlc.getDumpFileOptions();

			if (flagList.contains("colorize"))
			{
				assertTrue(actual.colorize);
			}
			else
			{
				assertFalse(actual.colorize);
			}
			
			if (flagList.contains("actionlabels"))
			{
				assertTrue(actual.actionLabels);
			}
			else
			{
				assertFalse(actual.actionLabels);
			}
			
			if (flagList.contains("snapshot"))
			{
				assertTrue(actual.snapshot);
			}
			else
			{
				assertFalse(actual.snapshot);
			}
		}
	}

	@Test
	public void testCoverageOptionSetsGlobalVariable()
	{
		final Integer inputValue = 23;
		final int expectedValue = inputValue * 60 * 1000;
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-coverage", inputValue.toString(), tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue, TLCGlobals.coverageInterval);
	}
	
	@Test
	public void testInvalidCoverageOption()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {"-coverage", "-2", tlaFile};
		assertFalse(tlc.handleParameters(args));
		
		tlc = new TLC();
		args = new String[] {"-coverage", "NotANumber", tlaFile};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testCheckpointOptionSetsGlobalVariable()
	{
		final Integer inputValue = 23;
		final int expectedValue = inputValue * 60 * 1000;
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-checkpoint", inputValue.toString(), tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue, TLCGlobals.chkptDuration);
	}
	
	@Test
	public void testInvalidCheckpointOption()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {"-checkpoint", "-2", tlaFile};
		assertFalse(tlc.handleParameters(args));
		
		tlc = new TLC();
		args = new String[] {"-checkpoint", "NotANumber", tlaFile};
		assertFalse(tlc.handleParameters(args));

		tlc = new TLC();
		args = new String[] {tlaFile, "-checkpoint"};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testDepthOptionSetsVariable()
	{
		final Integer expectedValue = 23;
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-depth", expectedValue.toString(), tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue.intValue(), tlc.getTraceDepth());
	}
	
	@Test
	public void testInvalidDepthOptions()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {"-depth", "NotANumber", tlaFile};
		assertFalse(tlc.handleParameters(args));

		tlc = new TLC();
		args = new String[] {tlaFile, "-depth"};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testSeedOptionSetsVariable()
	{
		final Long expectedValue = 23L;
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-seed", expectedValue.toString(), tlaFile};
		assertFalse(tlc.haveSeed());
		assertTrue(tlc.handleParameters(args));
		assertTrue(tlc.haveSeed());
		assertEquals(expectedValue.longValue(), tlc.getSeed());
	}
	
	@Test
	public void testInvalidSeedOptions()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {"-seed", "NotANumber", tlaFile};
		assertFalse(tlc.handleParameters(args));

		tlc = new TLC();
		args = new String[] {tlaFile, "-seed"};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testArilOptionSetsVariable()
	{
		final Long expectedValue = 23L;
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-aril", expectedValue.toString(), tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue.longValue(), tlc.getAril());
	}
	
	@Test
	public void testInvalidArilOptions()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {"-aril", "NotANumber", tlaFile};
		assertFalse(tlc.handleParameters(args));

		tlc = new TLC();
		args = new String[] {tlaFile, "-aril"};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testMaxSetSizeOptionSetsGlobalVariable()
	{
		final Integer expectedValue = 23;
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-maxSetSize", expectedValue.toString(), tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue.intValue(), TLCGlobals.setBound);
	}
	
	@Test
	public void testInvalidMaxSetSizeOptions()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {"-maxSetSize", "NotANumber", tlaFile};
		assertFalse(tlc.handleParameters(args));

		tlc = new TLC();
		args = new String[] {tlaFile, "-maxSetSize"};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testRecoverOptionSetsVariable()
	{
		final String inputValue = String.format("{0}some{0}file{0}path", FileUtil.separator);
		final String expectedValue = inputValue + FileUtil.separator;
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-recover", inputValue, tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue, tlc.getCheckpointRecoveryDirectory());
	}
	
	@Test
	public void testInvalidRecoverOptions()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {tlaFile, "-recover"};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testMetadirOptionSetsGlobalVariable()
	{
		final String inputValue = String.format("{0}some{0}file{0}path", FileUtil.separator);
		final String expectedValue = inputValue + FileUtil.separator;
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-metadir", inputValue, tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue, TLCGlobals.metaDir);
	}
	
	@Test
	public void testInvalidMetadirOptions()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {tlaFile, "-metadir"};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testUserFileOptionSetsVariable()
	{
		final String expectedValue = "someFileName";
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-userFile", expectedValue, tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue, tlc.getUserFile());
	}
	
	@Test
	public void testInvalidUserFileOptions()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {tlaFile, "-userFile"};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testWorkerOptionSetsGlobalVariable()
	{
		Integer expectedValue = 4;
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		String[] args = new String[] {"-workers", expectedValue.toString(), tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue.intValue(), TLCGlobals.getNumWorkers());
		
		expectedValue = 1;
		args = new String[] {"-workers", expectedValue.toString(), tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue.intValue(), TLCGlobals.getNumWorkers());
	}
	
	@Test
	public void testWorkerAutoOptionSetsGlobalVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;

		final Integer expectedValue = 128;
		Supplier<Integer> hostProcessorCount = () -> expectedValue;
		TLC tlc = new TLC(hostProcessorCount);
		String[] args = new String[] {"-workers", "auto", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue.intValue(), TLCGlobals.getNumWorkers());
		
		final Integer edgeCaseValue = 1;
		hostProcessorCount = () -> edgeCaseValue;
		tlc = new TLC(hostProcessorCount);
		args = new String[] {"-workers", "auto", tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(edgeCaseValue.intValue(), TLCGlobals.getNumWorkers());
	}
	
	@Test
	public void testInvalidWorkerOptions()
	{
		final Supplier<Integer> hostProcessorCount = () -> 0;
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC(hostProcessorCount);
		String[] args = new String[] {tlaFile, "-workers"};
		assertFalse(tlc.handleParameters(args));
		
		args = new String[] {"-workers", "0", tlaFile};
		assertFalse(tlc.handleParameters(args));
		
		args = new String[] {"-workers", "-1", tlaFile};
		assertFalse(tlc.handleParameters(args));
		
		args = new String[] {"-workers", "NotANumber", tlaFile};
		assertFalse(tlc.handleParameters(args));

		args = new String[] {"-workers", "auto", tlaFile};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testDfidOptionSetsGlobalVariable()
	{
		final Integer expectedValue = 4;
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-dfid", expectedValue.toString(), tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue.intValue(), TLCGlobals.DFIDMax);
	}
	
	@Test
	public void testInvalidDfidOptions()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {tlaFile, "-dfid"};
		assertFalse(tlc.handleParameters(args));
		
		args = new String[] {"-dfid", "-1", tlaFile};
		assertFalse(tlc.handleParameters(args));
		
		args = new String[] {"-dfid", "NotANumber", tlaFile};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testFpOptionSetsVariable()
	{
		final Integer expectedValue = FP64.Polys.length - 1;
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-fp", expectedValue.toString(), tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue.intValue(), tlc.getFingerprintFunctionIndex());
	}
	
	@Test
	public void testInvalidFpOptions()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {tlaFile, "-fp"};
		assertFalse(tlc.handleParameters(args));
		
		args = new String[] {"-fp", "-1", tlaFile};
		assertFalse(tlc.handleParameters(args));
		
		final Integer inputValue = FP64.Polys.length;
		args = new String[] {"-fp", inputValue.toString(), tlaFile};
		assertFalse(tlc.handleParameters(args));
		
		args = new String[] {"-fp", "NotANumber", tlaFile};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testFpMemOptionSetsVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final Double expectedValue = 0.8;
		TLC tlc = new TLC();
		String[] args = new String[] {"-fpmem", expectedValue.toString(), tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertTrue(expectedValue.doubleValue() == tlc.getFingerprintSetConfiguration().getRatio());
		
		final Double inputValue = 2048d;
		tlc = new TLC();
		args = new String[] {"-fpmem", inputValue.toString(), tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertTrue(1.0d == tlc.getFingerprintSetConfiguration().getRatio());
	}
	
	@Test
	public void testInvalidFpMemOptions()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {tlaFile, "-fpmem"};
		assertFalse(tlc.handleParameters(args));
		
		args = new String[] {"-fpmem", "-1", tlaFile};
		assertFalse(tlc.handleParameters(args));
		
		args = new String[] {"-fpmem", "NotANumber", tlaFile};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testFpBitsOptionSetsVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		final Integer expectedValue = 16;
		TLC tlc = new TLC();
		String[] args = new String[] {"-fpbits", expectedValue.toString(), tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(expectedValue.intValue(), tlc.getFingerprintSetConfiguration().getFpBits());
	}
	
	@Test
	public void testInvalidFpBitsOptions()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {tlaFile, "-fpbits"};
		assertFalse(tlc.handleParameters(args));
		
		args = new String[] {"-fpbits", "-1", tlaFile};
		assertFalse(tlc.handleParameters(args));
		
		final Integer inputValue = MultiFPSet.MAX_FPBITS + 1;
		args = new String[] {"-fpbits", inputValue.toString(), tlaFile};
		assertFalse(tlc.handleParameters(args));
		
		args = new String[] {"-fpbits", "NotANumber", tlaFile};
		assertFalse(tlc.handleParameters(args));
	}

	@Test
	public void testMainTlaFileSetsVariable()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {tlaFile};
		assertTrue(tlc.handleParameters(args));
		assertEquals(tlaFile, tlc.getMainFile());
	}

	@Test
	public void testInvalidMainTlaFile()
	{
		final String tlaFile = TLAConstants.Files.MODEL_CHECK_FILE_BASENAME;
		TLC tlc = new TLC();
		String[] args = new String[] {tlaFile, tlaFile};
		assertFalse(tlc.handleParameters(args));

		args = new String[] {"-"};
		assertFalse(tlc.handleParameters(args));
	}
}
