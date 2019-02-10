package tlc2.value.impl;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import org.junit.Test;

import tlc2.value.impl.IntValue;
import tlc2.value.impl.IntervalValue;
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
}
