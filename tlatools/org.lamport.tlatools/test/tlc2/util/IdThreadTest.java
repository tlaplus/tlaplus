package tlc2.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

import org.junit.Test;

import tlc2.value.impl.IntValue;

public class IdThreadTest {

	@Test
	public void testSetGetLocalValue() {
		final IdThread t = new IdThread(0);
		assertNull(t.getLocalValue(42));

		t.setLocalValue(1, IntValue.gen(1));
		t.setLocalValue(42, IntValue.gen(42));
		assertEquals(IntValue.gen(1), t.getLocalValue(1));
		assertEquals(IntValue.gen(42), t.getLocalValue(42));
		assertNull(t.getLocalValue(43));
	}
}
