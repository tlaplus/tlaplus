package tlc2;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;
import util.TLCRuntime;

public class TLCTest {

	@Test
	public void testHandleParametersAbsoluteInvalid() {
		final TLC tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-fpmem", "-1", "MC"}));
	}
	
	@Test
	public void testHandleParametersAbsoluteValid() {
		final TLC tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-fpmem", "101", "MC"}));
	}
	
	@Test
	public void testHandleParametersFractionInvalid() {
		final TLC tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-fpmem", "-0.5", "MC"}));
	}
	
	/**
	 * Allocating to little should result in min default
	 */
	@Test
	public void testHandleParametersAllocateLowerBound() {
		final TLC tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-fpmem", "0", "MC"}));
		assertEquals("Allocating to little should result in min default",
				TLCRuntime.MinFpMemSize, tlc.getFPSetConfiguration()
						.getMemoryInBytes());
	}
	
	/**
	 * Overallocating should result in max default
	 */
	@Test
	public void testHandleParametersAllocateUpperBound() {
		final TLC tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-fpmem", Long.toString(Long.MAX_VALUE), "MC"}));
        final long maxMemory = (long) (Runtime.getRuntime().maxMemory() * 0.75d);
		assertEquals("Overallocating should result in max default (75%)",
				maxMemory, tlc.getFPSetConfiguration().getMemoryInBytes());
	}
	
	/**
	 * .5 is valid
	 */
	@Test
	public void testHandleParametersAllocateHalf() {
		final TLC tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-fpmem", ".5", "MC"}));
        final long maxMemory = (long) (Runtime.getRuntime().maxMemory() * 0.50d);
		assertEquals("Overallocating should result in max default (50%)",
				maxMemory, tlc.getFPSetConfiguration().getMemoryInBytes());
	}
	
	/**
	 * .99 is valid
	 */
	@Test
	public void testHandleParametersAllocate90() {
		final TLC tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-fpmem", ".99", "MC"}));
        final long maxMemory = (long) (Runtime.getRuntime().maxMemory() * 0.99d);
		assertEquals("Overallocating should result in max default (99%)",
				maxMemory, tlc.getFPSetConfiguration().getMemoryInBytes());
	}
	
	/**
	 *  is valid
	 */
	@Test
	public void testHandleParametersMaxSetSize() {
		final int progDefault = TLCGlobals.setBound;
		
		TLC tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-maxSetSize", "NaN", "MC"}));
		
		tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-maxSetSize", "0", "MC"}));
		tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-maxSetSize", "-1", "MC"}));
		tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-maxSetSize", Integer.toString(Integer.MIN_VALUE), "MC"}));
		
		tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-maxSetSize", "1", "MC"}));
		assertTrue(TLCGlobals.setBound == 1);
		

		tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-maxSetSize", Integer.toString(progDefault), "MC"}));
		assertTrue(TLCGlobals.setBound == progDefault);
		
		tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-maxSetSize", Integer.toString(Integer.MAX_VALUE), "MC"}));
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
}
