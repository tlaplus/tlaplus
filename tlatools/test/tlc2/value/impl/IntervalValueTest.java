package tlc2.value.impl;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;

import util.Assert.TLCRuntimeException;

public class IntervalValueTest {

	@Test
	public void testElementAt() {
		final IntervalValue iv = new IntervalValue(3, 11);
		for (int i = 0; i < iv.size(); i++) {
			assertEquals(IntValue.gen(i + 3), iv.elementAt(i));
		}
	}

	@Test
	public void testElementAtOutOfBoundsNegative() {
		final IntervalValue iv = new IntervalValue(3, 11);
		try {
			iv.elementAt(-1);
		} catch (TLCRuntimeException e) {
			return;
		}
		fail();
	}

	@Test
	public void testElementAtOutOfBoundsSize() {
		final IntervalValue iv = new IntervalValue(3, 11);
		try {
			iv.elementAt(iv.size());
		} catch (TLCRuntimeException e) {
			return;
		}
		fail();
	}
	
	@Test
	public void sizeOverflow() {
		assertEquals(Integer.MAX_VALUE, new IntervalValue(1, Integer.MAX_VALUE).size());
		assertEquals(Integer.MAX_VALUE, new IntervalValue(Integer.MIN_VALUE, -2).size());
		
		try {
			assertEquals(0, new IntervalValue(-989_822_976, 1_157_660_672).size());
		} catch (TLCRuntimeException e) {
			assertTrue(e.getMessage().contains("Size of interval value exceeds the maximum representable size (32bits)"));
			return;
		}
		fail();
	}
	
	@Test
	public void compareToOverflow1() {
		final IntervalValue iv = new IntervalValue(Integer.MAX_VALUE - 1, Integer.MAX_VALUE);
		assertEquals(2, iv.size());
		
		final IntervalValue iv2 = new IntervalValue(Integer.MIN_VALUE + 1, Integer.MIN_VALUE + 2);
		assertEquals(2, iv2.size());
		
		assertEquals(1, iv.compareTo(iv2));
	}
}
