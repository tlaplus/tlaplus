package tlc2.tool.fp;

import static org.junit.Assert.assertEquals;

import org.junit.Assume;
import org.junit.Before;
import org.junit.Test;

import tlc2.tool.fp.OffHeapDiskFPSet.Iterator;

public class OffHeapIteratorTest {
	
	@Before
	public void setup() {
		Assume.assumeTrue(LongArray.isSupported());
	}

	@Test
	public void testNext() {
		final long elements = 32L;
		final LongArray array = new LongArray(2L * elements);
		for (int i = 0; i < array.size(); i++) {
			array.set(i, i+1);
		}

		final Iterator itr = new OffHeapDiskFPSet.Iterator(array, elements,
				new OffHeapDiskFPSet.Indexer(2L * elements, 1));

		long actual = 1L;
		while (itr.hasNext()) {
			long next = itr.next();
			assertEquals(actual, next);
			actual++;
		}
		assertEquals(elements, actual - 1);
		
		for (int i = 0; i < array.size(); i++) {
			assertEquals(i + 1, array.get(i));
		}
	}

	@Test
	public void testMarkNext() {
		final int elements = 32;
		final LongArray array = new LongArray(2L * elements);
		for (int i = 0; i < array.size(); i++) {
			array.set(i, i+1);
		}

		final Iterator itr = new OffHeapDiskFPSet.Iterator(array, elements,
				new OffHeapDiskFPSet.Indexer(2L * elements, 1));

		long actual = 1L;
		while (itr.hasNext()) {
			long next = itr.markNext();
			assertEquals(actual, next);
			actual++;
		}
		assertEquals(elements, actual - 1);
		
		for (int i = elements; i < array.size(); i++) {
			assertEquals(elements + 1, array.get(elements));
		}
		for (int i = 0; i < elements; i++) {
			long expected = i + 1 | 0x8000000000000000L;
			actual = array.get(i);
			assertEquals(expected, actual);
		}
	}
}
