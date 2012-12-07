// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import tlc2.output.EC;
import util.Assert;

import sun.misc.Unsafe;

@SuppressWarnings("restriction")
public final class OffHeapDiskFPSetHelper {

	private OffHeapDiskFPSetHelper() {
		// no instantiation!
	}

	/**
	 * @return An Unsafe object or a {@link RuntimeException} wrapping any {@link Exception}. 
	 */
	public static sun.misc.Unsafe getUnsafe() {
		try {
			// Use reflection API to unhide Unsafe
			final Field f = sun.misc.Unsafe.class.getDeclaredField("theUnsafe");
			f.setAccessible(true);
			return (sun.misc.Unsafe) f.get(null);
		} catch (Exception e) {
			throw new RuntimeException(
					"Trying to use Sun VM specific sun.misc.Unsafe implementation but no Sun based VM detected.",
					e);
		}
	}
	
	/**
	 * Initializes the memory by overriding each byte with zero starting at
	 * <code>baseAddress</code> and ending when <code>fingerprintCount</code>
	 * bytes have been written.
	 * <p>
	 * To speed up the initialization, <code>numThreads</code> allows to set a
	 * thread count with which zeroing is then done in parallel.
	 * 
	 * @param u
	 * @param baseAddress Base address of the (previously) allocated memory 
	 * @param numThreads Number of threads used to zero memory
	 * @param fingerprintCount Number of fingerprint for which the memory should be initialized
	 * @throws IOException
	 */
	public static void zeroMemory(final Unsafe u, final long baseAddress, int numThreads, final long fingerprintCount)
			throws IOException {
		
		final int addressSize = u.addressSize();
		final long segmentSize = fingerprintCount / numThreads;

		final ExecutorService es = Executors.newFixedThreadPool(numThreads);
		try {
			final Collection<Callable<Boolean>> tasks = new ArrayList<Callable<Boolean>>(numThreads);
			for (int i = 0; i < numThreads; i++) {
				final int offset = i;
				tasks.add(new Callable<Boolean>() {

					public Boolean call() throws Exception {
						// Null memory (done in parallel on segments).
						// This is essential as allocateMemory returns
						// uninitialized memory and
						// memInsert/memLockup utilize 0L as a mark for an
						// unused fingerprint slot.
						// Otherwise memory garbage wouldn't be distinguishable
						// from a true fp.
						final long lowerBound = segmentSize * offset;
						final long upperBound = (1 + offset) * segmentSize;
						for (long i = lowerBound; i < upperBound; i++) {
							final long address = baseAddress + (i * addressSize);
							u.putAddress(address, 0L);
						}
						return true;
					}
				});
			}
			final List<Future<Boolean>> invokeAll = es.invokeAll(tasks);
			Assert.check(!invokeAll.isEmpty(), EC.GENERAL);
		} catch (InterruptedException e) {
			// not expected to happen
			e.printStackTrace();
		} finally {
			es.shutdown();
		}
	}
}
