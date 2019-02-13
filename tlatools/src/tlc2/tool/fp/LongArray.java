// Copyright (c) 2016 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

/*
 * On Java 11 (probably starting with 9) sun.misc.Unsafe is implemented on top
 * of jdk.internal.misc.Unsafe which provides a similar though not quiet
 * identical API.  While sun.misc.Unsafe remains available to client code such
 * as LongArray in Java 11, parts of its API have already been dissolved
 * (see e.g. https://bugs.openjdk.java.net/browse/JDK-8202999).  This does not
 * affect LongArray yet, but will probably affect LongArray in the future. 
 * Refactoring LongArray to replace sun.misc.Unsafe with jdk.internal.misc.Unsafe
 * requires the following changes:
 * - Replace sun.misc.Unsafe with jdk.internal.misc.Unsafe
 * - Change Unsafe#compareAndSwapLong with Unsafe#compareAndSetLong in LongArray#trySet
 * - Run LongArray on Java 11 with "--add-opens=java.base/jdk.internal.misc=ALL-UNNAMED"
 *   to configure Java's module system (Jigsaw) to expose jdk.internal.misc.Unsafe
 *   to LongArray.
 * The last requirement is visible to TLA+ users who run tla2tools.jar on the
 * command-line.  As we do not want to expose JVM parameters to them, we keep
 * sun.misc.Unsafe for now.
 */
import sun.misc.Unsafe; // jdk.internal.misc.Unsafe;
import tlc2.output.EC;
import util.Assert;
import util.TLCRuntime;

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

	/**
	 * Maximum number of elements that can be contained in this array.
	 */
	private final long length;
	
	/**
	 * CHOOSE logAddressSize \in 1..(Long.SIZE / 8): 2^logAddressSize = (Long.SIZE / 8)
	 */
	private static final int logAddressSize = 3;

	LongArray(final long positions) {
		this.length = positions;
		this.unsafe = getUnsafe();
		
		// LongArray is only implemented for 64bit architectures. A 32bit
		// implementation might be possible. However, implementing CAS (see
		// trySet) seems impossible when values have to be split in two
		// parts (low/hi) on a 32 bit architecture.
		// addressSize(): Report the size in bytes of a native pointer, as
		// stored via #putAddress . This value will be either 4 or 8. We
		// expect 8 (Long.SIZE / 8) which is the size of a TLC fingerprint
		// (see FP64).
		Assert.check(this.unsafe.addressSize() == (Long.SIZE / 8), EC.GENERAL);
		baseAddress = this.unsafe.allocateMemory(positions << logAddressSize);
	}
	
	LongArray(final Collection<Long> from) {
		this(from.size());
		
		final Iterator<Long> itr = from.iterator();
		long i = 0L;
		while(itr.hasNext()) {
			Long next = itr.next();
			set(i++, next);
		}
	}

	/**
	 * @return true iff LongArray can be used on the current JVM. It cannot be used
	 *         if the architecture is not 64 bit and the sun.misc.Unsafe class
	 *         cannot be loaded (on some JVM implementations, this isn't possible).
	 */
	public static boolean isSupported() {
		if (TLCRuntime.ARCH.x86_64 != TLCRuntime.getInstance().getArchitecture()) {
			return false;
		}
		try {
			if (getUnsafe() != null) {
				return true;
			}
			return false;
		} catch (RuntimeException e) {
			return false;
		}
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
	 * <code>baseAddress</code> and ending when all positions have been written.
	 * 
	 * @throws IOException
	 */
	public final void zeroMemory()
			throws IOException {
		this.unsafe.setMemory(baseAddress, length * 8L, (byte) 0); // times 8L because it only writes a single byte.
	}
	
	/**
	 * Initializes the memory by overriding each byte with zero starting at
	 * <code>baseAddress</code> and ending when all positions have been written.
	 * <p>
	 * To speed up the initialization, <code>numThreads</code> allows to set a
	 * thread count with which zeroing is done in parallel.
	 * 
	 * @param numThreads
	 *            Number of threads used to zero memory
	 * @throws IOException
	 */
	public final void zeroMemory(final int numThreads)
			throws IOException {

		final long segmentSize = (long) Math.floor(length / numThreads);
		
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
						// unused fingerprint position.
						// Otherwise memory garbage wouldn't be distinguishable
						// from a true fp.
						final long lowerBound = segmentSize * offset;
						// The last threads zeros up to the end.
						final long upperBound = offset == numThreads - 1 ? length : (1 + offset) * segmentSize;
						for (long pos = lowerBound; pos < upperBound; pos++) {
							set(pos, 0L);
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
	
    private final void rangeCheck(final long position) {
		assert position >= 0 && position < this.length;
    }
	
	/**
	 * CAS (compare and swap) variant of {@link LongArray#set(long, long)}.
	 * 
	 * @param position
	 * @param expected
	 * @param value
	 * @return true iff successful 
     * @throws IndexOutOfBoundsException
	 */
	public final boolean trySet(final long position, final long expected, final long value) {
		rangeCheck(position);
		return this.unsafe.compareAndSwapLong(null, log2phy(position), expected, value);
	}
	
    /**
     * Inserts the specified element at the specified position in this
     * array. Overwrites any previous occupant of the specified position.
     *
     * @param position position at which the specified element is to be inserted
     * @param value element to be inserted
     * @throws IndexOutOfBoundsException
     */
	public final void set(final long position, final long value) {
		rangeCheck(position);
		this.unsafe.putAddress(log2phy(position), value);
	}

    /**
     * Returns the element at the specified position in this array.
     *
     * @param  position position of the element to return
     * @return the element at the specified position in this array
     * @throws IndexOutOfBoundsException
     */
	public final long get(final long position) {
		rangeCheck(position);
		return this.unsafe.getAddress(log2phy(position));
	}

	/**
	 * Swaps elements at pos1 and pos2. This is not atomic. The element at pos1
	 * will for a moment not be an element of {@link LongArray}.
	 */
	public final void swap(final long position1, final long position2) {
		rangeCheck(position1);
		rangeCheck(position2);
		final long tmp = get(position1);
		set(position1, get(position2));
		set(position2, tmp);
	}
	
	/*
	 * Variant of swap that uses copyMemory. This implementation - suprisingly - is
	 * *not* faster compared to swap above (see LongArrayBenchmark).
	 */
	void swapCopy(final long position1, final long position2) {
		final long tmp = unsafe.getAddress(log2phy(position1));
		unsafe.copyMemory(log2phy(position2), log2phy(position1), 8L);
		unsafe.putAddress(log2phy(position2), tmp);
	}

	
    /**
     * Returns the number of elements in this array.
     *
     * @return the number of elements in this array
     */
	public final long size() {
		return length;
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return toString(0L, length - 1L);
	}

	public String toString(long start, long end) {
        long iMax = end;
        if (iMax == -1L) {
        	return "[]";
        }

        final StringBuilder b = new StringBuilder();
        b.append('[');
        for (long i = start; ; i++) {
            final long lng = get(i);
            if (lng == 0L) {
            	b.append("e");
            } else {
            	b.append(lng);
            }
            if (i == iMax) {
            	return b.append(']').toString();
            }
            b.append(", ");
        }
	}
	
	public static void main(final String[] args) throws IOException {
		final long elements = 1L << Integer.valueOf(args[0]);
		System.out.format("Allocating LongArray with %,d elements.\n", elements);
		final LongArray longArray = new LongArray(elements);
		longArray.zeroMemory();
	}
}
