package tlc2;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assume.assumeTrue;

import org.junit.Test;

import tlc2.tool.fp.FPSetConfiguration;
import tlc2.tool.fp.FPSetFactory;
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
		assertTrue(tlc.handleParameters(args, true));
		final FPSetConfiguration fpSetConfiguration = tlc.getFPSetConfiguration();
		assumeTrue(FPSetFactory.allocatesOnHeap(fpSetConfiguration.getImplementation()));
		assertEquals("Allocating to little should result in min default",
				TLCRuntime.MinFpMemSize, fpSetConfiguration
						.getMemoryInBytes());
	}
	
	/**
	 * Overallocating should result in max default
	 */
	@Test
	public void testHandleParametersAllocateUpperBound() {
		final TLC tlc = new TLC();
		final String[] args = new String[] {"-fpmem", Long.toString(Long.MAX_VALUE), TLAConstants.Files.MODEL_CHECK_FILE_BASENAME};
		assertTrue(tlc.handleParameters(args, true));
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
		assertTrue(tlc.handleParameters(args, true));
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
		assertTrue(tlc.handleParameters(args, true));
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
		assertFalse(tlc.handleParameters(new String[] {"-maxSetSize", "NaN", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME}));
		
		tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-maxSetSize", "0", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME}));
		tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-maxSetSize", "-1", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME}));
		tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] { "-maxSetSize", Integer.toString(Integer.MIN_VALUE),
				TLAConstants.Files.MODEL_CHECK_FILE_BASENAME }));
		
		tlc = new TLC();
		final String[] args = new String[] {"-maxSetSize", "1", TLAConstants.Files.MODEL_CHECK_FILE_BASENAME};
		assertTrue(tlc.handleParameters(args, true));
		assertTrue(TLCGlobals.setBound == 1);
		

		tlc = new TLC();
		final String[] args2 = new String[] { "-maxSetSize", Integer.toString(progDefault), TLAConstants.Files.MODEL_CHECK_FILE_BASENAME };
		assertTrue(tlc.handleParameters(args2, true));
		assertTrue(TLCGlobals.setBound == progDefault);
		
		tlc = new TLC();
		final String[] args3 = new String[] { "-maxSetSize", Integer.toString(Integer.MAX_VALUE), TLAConstants.Files.MODEL_CHECK_FILE_BASENAME};
		assertTrue(tlc.handleParameters(args3, true));
		assertTrue(TLCGlobals.setBound == Integer.MAX_VALUE);
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
		assertTrue(tlc.handleParameters(args, true));
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
		assertTrue(tlc.handleParameters(args, true));
		assertEquals(TLC.RunMode.SIMULATE, tlc.getRunMode());
		assertEquals(expectedLimit, tlc.getSimulationBehaviorCountLimit());
		assertEquals(expectedPath, tlc.getTraceFilePath());
	}
}
