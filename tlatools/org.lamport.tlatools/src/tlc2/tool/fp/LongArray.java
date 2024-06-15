// Copyright (c) 2016 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp;

import java.lang.foreign.Arena;
import java.lang.foreign.MemorySegment;
import java.lang.foreign.SegmentAllocator;
import java.lang.foreign.ValueLayout;
import java.lang.invoke.MethodHandles;
import java.lang.invoke.VarHandle;
import java.util.Collection;

/**
 * This class manually allocates & manages memory. It does this because Java
 * datastructures are limited to using signed ints for capacity & indexing;
 * this limits size to approximately 2 billion elements, which TLC can easily
 * exceed. By allocating memory ourselves we can use a 64-bit long for both
 * capacity and indexing.
 *
 * Before using the newer java.lang.foreign and java.lang.invoke Foreign
 * Function & Memory (FFM) APIs, this class used sun.misc.Unsafe. That API
 * was deprecated; see https://openjdk.org/jeps/471
 *
 * Code & understanding adapted from the following StackOverflow questions:
 * - Allocating MemorySegment: https://stackoverflow.com/q/78587689/2852699
 * - How to CAS with VarHandle: https://stackoverflow.com/q/78599864/2852699
 * - On layout alignment: https://stackoverflow.com/q/78624634/2852699
 * - 32-bit compatibility: https://stackoverflow.com/q/78625226/2852699
 * - Segment logical length: https://stackoverflow.com/q/78640041/2852699
 */
public final class LongArray {

	/**
	 * Allocator managing the memory lifetime; in the global scope, memory is
	 * never deallocated until the process terminates.
	 */
	private final SegmentAllocator allocator = Arena.global();

	/**
	 * The layout of the allocated memory.
	 */
	private final ValueLayout.OfLong layout = ValueLayout.JAVA_LONG;

	/**
	 * Segment holding the allocated memory.
	 */
	private final MemorySegment segment;

	/**
	 * The handle to use for atomic compare-and-set (CAS) operations.
	 */
	private final VarHandle handle;

	/**
	 * Constructs a zeroed array of the given capacity.
	 *
	 * @param capacity The maximum number of longs the array can hold.
	 */
	LongArray(final long capacity) {
		assertSupported();
		this.segment = this.allocator.allocate(this.layout, capacity);
		this.handle = fixHandleParameters(this.layout, this.segment);
	}
	
	/**
	 * Constructs a long array populated with the provided data.
	 *
	 * @param from The data with which to populate the array.
	 */
	public LongArray(final long[] from) {
		assertSupported();
		this.segment = this.allocator.allocateFrom(this.layout, from);
		this.handle = fixHandleParameters(this.layout, this.segment);
	}

	/**
	 * Constructs a VarHandle instance with some fixed parameters since we will
	 * only ever use it to access the particular given MemorySegment.
	 *
	 * @param layout The layout to fix in the VarHandle.
	 * @param MemorySegment The memory segment to fix in the VarHandle.
	 * @return A VarHandle instance fixed with the given parameters.
	 */
	private static VarHandle fixHandleParameters(
			final ValueLayout.OfLong layout,
			final MemorySegment segment
		) {
		return MethodHandles.insertCoordinates(
				layout.arrayElementVarHandle(), 0, segment, 0L);
	}

	/**
	 * Assert that this class is supported on the current system architecture,
	 * failing with an error message if not.
	 */
	private static void assertSupported() {
		assert isSupported() : "LongArray requires a 64-bit system architecture.";
	}

	/**
	 * Whether this class can be used on the current system architecture. This
	 * class requires 64-bit address width for atomic compare-and-set, as
	 * otherwise word tearing occurs when reading & writing 64-bit longs in CAS
	 * operations (which will simply fail with an exception).
	 *
	 * @return Whether LongArray is supported on this system architecture.
	 */
	public static boolean isSupported() {
		return ValueLayout.ADDRESS.byteSize() == ValueLayout.JAVA_LONG.byteSize();
	}

	/**
	 * CAS (compare-and-set) variant of {@link LongArray#set(long, long)}.
	 *
	 * @param index The index to compare/swap.
	 * @param expected The expected value in the index.
	 * @param value The value to write if expected value is found.
	 * @return Whether array index was written.
	 */
	public final boolean trySet(final long index, final long expected, final long value) {
		return this.handle.compareAndSet(index, expected, value);
	}
	
	/**
	 * Sets the given index to the given value.
	 *
	 * @param index The index to write.
	 * @param value The value to write to the index.
	 */
	public final void set(final long index, final long value) {
		this.segment.setAtIndex(this.layout, index, value);
	}

	/**
	 * Gets the value at the given index.
	 *
	 * @param index The index to read.
	 * @return The value at the given index.
	 */
	public final long get(final long index) {
		return this.segment.getAtIndex(this.layout, index);
	}

	/**
	 * Swaps elements at pos1 and pos2. This is not atomic. The element at pos1
	 * will for a moment not be an element of {@link LongArray}.
	 *
	 * @param position1 The first index to swap.
	 * @param position2 The second index to swap.
	 */
	public final void swap(final long position1, final long position2) {
		final long tmp = this.get(position1);
		this.set(position1, this.get(position2));
		this.set(position2, tmp);
	}
	
	/**
	 * Returns the capacity of this array.
	 *
	 * @return The capacity of this array.
	 */
	public final long size() {
		// The size of the stream is known so count() returns immediately.
		// https://stackoverflow.com/a/78640168/2852699
		return this.segment.elements(this.layout).count();
	}
	
	/**
	 * Dumps the contents of this array into a string.
	 *
	 * @see java.lang.Object#toString()
	 * @return A string representation of the array.
	 */
	public String toString() throws IndexOutOfBoundsException {
		assert this.size() <= (long)Integer.MAX_VALUE : "LongArray is too long to convert to a string.";
		return toString(0L, this.size() - 1L);
	}

	/**
	 * Dumps a subsequence of this array to a string.
	 *
	 * @param start The index to begin reading.
	 * @param end The index to end reading (inclusive).
	 * @return A string representation of the array.
	 */
	public String toString(long start, long end) throws IndexOutOfBoundsException {
		long iMax = end;
		if (iMax == -1L) {
			return "[]";
		}

		assert start <= end : "Subsequence end index must be higher than start index.";
		assert Math.abs(Math.subtractExact(end, start)) <= (long)Integer.MAX_VALUE : "LongArray subsequence is too long to convert to a string.";

		final StringBuilder b = new StringBuilder();
		b.append('[');
		for (long i = start; ; i++) {
			final long lng = this.get(i);
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
}
