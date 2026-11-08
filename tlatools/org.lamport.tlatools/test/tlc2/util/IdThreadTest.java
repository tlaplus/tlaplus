package tlc2.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;
import static org.junit.Assert.assertNull;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

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

	// https://github.com/tlaplus/tlaplus/issues/1486
	@Test
	public void testConcurrentSetLocalValue() throws Exception {
		final int threads = 8;
		final int perThread = 64;
		final ExecutorService pool = Executors.newFixedThreadPool(threads);
		try {
			for (int iter = 0; iter < 500; iter++) {
				final IdThread target = new IdThread(0);
				final CountDownLatch start = new CountDownLatch(1);
				final List<Future<?>> futures = new ArrayList<>();
				for (int t = 0; t < threads; t++) {
					final int offset = t;
					futures.add(pool.submit(() -> {
						start.await();
						for (int i = 0; i < perThread; i++) {
							final int idx = i * threads + offset;
							target.setLocalValue(idx, IntValue.gen(idx));
						}
						return null;
					}));
				}
				start.countDown();
				for (Future<?> f : futures) {
					f.get();
				}
				for (int idx = 0; idx < threads * perThread; idx++) {
					final IntValue v = (IntValue) target.getLocalValue(idx);
					assertNotNull("Lost write at index " + idx, v);
					assertEquals(idx, v.val);
				}
			}
		} finally {
			pool.shutdownNow();
		}
	}
}
