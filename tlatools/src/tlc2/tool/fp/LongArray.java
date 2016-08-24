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

import sun.misc.Unsafe;
import tlc2.output.EC;
import util.Assert;

/**
 * This implementation uses sun.misc.Unsafe instead of a wrapping
 * java.nio.ByteBuffer due to the fact that the former's allocateMemory
 * takes a long argument, while the latter is restricted to
 * Integer.MAX_VALUE as its capacity.<br>
 * In 2012 this poses a too hard limit on the usable memory, hence we trade
 * generality for performance.
 */
@SuppressWarnings("restriction")
public final class LongArray {

	private final Unsafe unsafe;
	
	/**
	 * The base address of this direct memory allocated with Unsafe.
	 */
	private final long baseAddress;
	
	private final int logAddressSize;

	/**
	 * Maximum number of elements that can be contained in this array.
	 */
	private final long positions;

	LongArray(final long positions) {
		this.positions = positions;
		this.unsafe = getUnsafe();
		
		// Determine base address which varies depending on machine architecture.
		int addressSize = addressSize();
		
		int cnt = -1;
		while (addressSize > 0) {
			cnt++;
			addressSize = addressSize >>> 1; // == (n/2)
		}
		logAddressSize = cnt;

		// Allocate non-heap memory
		long bytes = positions << logAddressSize;
		baseAddress = allocateMemory(bytes);
	}

	/**
	 * @return An Unsafe object or a {@link RuntimeException} wrapping any {@link Exception}. 
	 */
	private static sun.misc.Unsafe getUnsafe() {
		// More Details can be found at: http://www.mydailyjava.blogspot.no/2013/12/sunmiscunsafe.html
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
	 * @param numThreads Number of threads used to zero memory
	 * @throws IOException
	 */
	public final void zeroMemory(final int numThreads)
			throws IOException {
		
		final int addressSize = addressSize();
		final long segmentSize = positions / numThreads;

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
							unsafe.putAddress(address, 0L);
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

	private long allocateMemory(long bytes) {
		return this.unsafe.allocateMemory(bytes);
	}

	private int addressSize() {
		return this.unsafe.addressSize();
	}

	/**
	 * Converts from logical positions to 
	 * physical memory addresses.
	 * 
	 * @param logical position (zero indexed)
	 * @return The physical address of the fp slot
	 */
	private final long log2phy(long logicalAddress) {
		return baseAddress + (logicalAddress << logAddressSize);
	}
	
    private void rangeCheck(final long position) {
		// Might want to replace with assert eventually to avoid comparison on
		// each set/get.
		//assert position >= 0 && position < this.positions;
    	
        if (position < 0 || position >= positions) {
        	throw new IndexOutOfBoundsException("Index: "+position+", Size: "+positions);
        }
    }
	
	/**
	 * CAS (compare and swap)
	 * 
	 * @param position
	 * @param expected
	 * @param value
	 * @return true iff successful 
	 */
	public final boolean trySet(final long position, final long expected, final long value) {
		rangeCheck(position);
		return this.unsafe.compareAndSwapLong(null, log2phy(position), expected, value);
	}
	
	public final void set(final long position, final long value) {
		rangeCheck(position);
		this.unsafe.putAddress(log2phy(position), value);
	}

	public final long get(final long position) {
		rangeCheck(position);
		return this.unsafe.getAddress(log2phy(position));
	}
}
