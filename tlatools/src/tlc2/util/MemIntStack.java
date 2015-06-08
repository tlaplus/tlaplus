// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:33 PST by lamport
//      modified on Thu Jan 10 18:33:42 PST 2002 by yuanyu

package tlc2.util;

public final class MemIntStack extends MemBasedSet {
	private static final int MIN_CAPACITY = 1024;

	public MemIntStack(String diskdir, String name) {
		// TODO Implement flushing MemIntStack to disk when it becomes too
		// large. This might not be necessary though, when concurrent SCC
		// search is implemented first. Its implementation will either replace
		// MemIntStack completely with something different or make sure that
		// each thread uses its own MemIntStack thus splitting the space 
		// requirement among the threads (avoid NegativeArraySizeException).
		super(MIN_CAPACITY);
	}

	/**
	 * Push an integer onto the stack.
	 */
	public final synchronized void pushInt(int x) {
		if (this.size == this.elems.length) {
			final int[] newElems = ensureCapacity(MIN_CAPACITY);
			System.arraycopy(elems, 0, newElems, 0, this.size);
			this.elems = newElems;
		}
		this.elems[this.size] = x;
		this.size++;
	}

	/**
	 * Push a long integer onto the stack.
	 */
	public final synchronized void pushLong(long x) {
		this.pushInt((int) (x & 0xFFFFFFFFL));
		this.pushInt((int) (x >>> 32));
	}

	/**
	 * Pop the integer on top of the stack.
	 */
	public final synchronized int popInt() {
		return this.elems[--this.size];
	}

	public final synchronized int peakInt() {
		return peakInt(size - 1);
	}

	public final synchronized int peakInt(int pos) {
		return this.elems[pos];
	}

	/**
	 * Pop the long integer on top of the stack.
	 */
	public final synchronized long popLong() {
		long high = this.popInt();
		long low = this.popInt();
		return (high << 32) | (low & 0xFFFFFFFFL);
	}

	public final synchronized long peakLong() {
		long high = this.peakInt();
		long low = this.peakInt();
		return (high << 32) | (low & 0xFFFFFFFFL);
	}

	public final synchronized long peakLong(int pos) {
		long high = this.peakInt(pos + 1);
		long low = this.peakInt(pos);
		return (high << 32) | (low & 0xFFFFFFFFL);
	}

	/**
	 * Removes all elements from the stack
	 */
	public final void reset() {
		this.size = 0;
	}
}
