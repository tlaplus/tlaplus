package tlc2;

import junit.framework.TestCase;

public class TLCTest extends TestCase {

	/**
	 * fpmem and fpmemratio don't go along together
	 */
	public void testHandleParameters() {
		final TLC tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-fpmem", "500", "-fpmemratio", "1", "MC"}));
		assertFalse(tlc.handleParameters(new String[] {"-fpmemratio", "1", "-fpmem", "500", "MC"}));
	}

	public void testHandleParametersInvalidLowerBound() {
		final TLC tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-fpmemratio", "-1", "MC"}));
	}
	
	public void testHandleParametersInvalidUpperBound() {
		final TLC tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-fpmemratio", "101", "MC"}));
	}
	
	public void testHandleParametersInvalidFraction() {
		final TLC tlc = new TLC();
		assertFalse(tlc.handleParameters(new String[] {"-fpmemratio", "0.5", "MC"}));
	}
	
	/**
	 * Allocating to little should result in min default
	 */
	public void testHandleParametersAllocateLowerBound() {
		final TLC tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-fpmemratio", "0", "MC"}));
		assertEquals("Allocating to little should result in min default", TLC.MinFpMemSize, tlc.getFpMemSize());
	}
	
	/**
	 * Overallocating should result in max default
	 */
	public void testHandleParametersAllocateUpperBound() {
		final TLC tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-fpmemratio", "100", "MC"}));
        final long maxMemory = (long) (Runtime.getRuntime().maxMemory() * 0.75d);
		assertEquals("Overallocating should result in max default (75%)", maxMemory, tlc.getFpMemSize());
	}
	
	/**
	 * .5 is valid
	 */
	public void testHandleParametersAllocateHalf() {
		final TLC tlc = new TLC();
		assertTrue(tlc.handleParameters(new String[] {"-fpmemratio", "50", "MC"}));
        final long maxMemory = (long) (Runtime.getRuntime().maxMemory() * 0.50d);
		assertEquals("Overallocating should result in max default (50%)", maxMemory, tlc.getFpMemSize());
	}
}
