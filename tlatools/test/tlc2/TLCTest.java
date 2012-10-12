package tlc2;

import util.TLCRuntime;
import junit.framework.TestCase;

public class TLCTest extends TestCase {

	public void testHandleParametersAbsoluteInvalid() {
		final TLC tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-fpmem", "-1", "MC"}));
	}
	
	public void testHandleParametersAbsoluteValid() {
		final TLC tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-fpmem", "101", "MC"}));
	}
	
	public void testHandleParametersFractionInvalid() {
		final TLC tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-fpmem", "-0.5", "MC"}));
	}
	
	/**
	 * Allocating to little should result in min default
	 */
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
}
