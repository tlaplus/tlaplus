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

	@Test
	public void testCompareExtremeIntervals() {
		final IntervalValue x = new IntervalValue(Integer.MIN_VALUE, -2);
		final IntervalValue y = new IntervalValue(1, Integer.MAX_VALUE);
		assertEquals(x.size(), y.size());
		assertTrue(x.compareTo(y) < 0);
		assertTrue(y.compareTo(x) > 0);
	}

	@Test
	public void testEmptyIntervalEquality() {
		IntervalValue i1 = new IntervalValue(10, 1);
		IntervalValue i2 = new IntervalValue(20, 15);
		assertEquals(i1, i2);
	}

	@Test
	public void testCompareEmptyIntervals() {
		int cmp = new IntervalValue(10, 1).compareTo(new IntervalValue(20, 15));
		assertEquals(0, cmp);
	}

	@Test
	public void testSizeOfMaximumRepresentableInterval() {
		final IntervalValue iv = new IntervalValue(Integer.MIN_VALUE, Integer.MAX_VALUE);
		try {
			iv.size();
		} catch (TLCRuntimeException e) {
			assertTrue(e.getMessage().contains("Size of interval value exceeds the maximum representable size (32bits)"));
			return;
		}
		fail();
	}

	@Test
	public void testExtremeIntervalSize() {
		final IntervalValue iv1 = new IntervalValue(Integer.MAX_VALUE, Integer.MAX_VALUE);
		assertEquals(1, iv1.size());
		final IntervalValue iv2 = new IntervalValue(Integer.MIN_VALUE, Integer.MIN_VALUE);
		assertEquals(1, iv2.size());
		final IntervalValue iv3 = new IntervalValue(Integer.MAX_VALUE-10, Integer.MAX_VALUE);
		assertEquals(11, iv3.size());
		final IntervalValue iv4 = new IntervalValue(Integer.MIN_VALUE, Integer.MIN_VALUE+10);
		assertEquals(11, iv4.size());
	}

}
