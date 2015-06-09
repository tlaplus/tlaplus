/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package tlc2.util;

public abstract class MemBasedSet {

	protected int size;

	protected int[] elems;

	public MemBasedSet(final int minCapacity) {
		this.size = 0;
		this.elems = new int[minCapacity];
	}
	
	protected int[] ensureCapacity(final int minCapacity) {
		// If the internal storage reaches its capacity, double the size of
		// the internal storage. This strategy is great for as long as size
		// is smaller than 2^31. Once size is >= 2^31, doubling it means it
		// becomes negative resulting in a NegativeArraySizeException. Additionally
		// if size gets larger and larger, an OutOfMemory exception becomes 
		// more likely when MemIntStacks memory requirements get doubled.
		// From the literature and popular implementations (e.g. Java's ArrayList),
		// a growth factor of 1.5 seems to be practical.
		final int newSize = (int) ((this.size * 3L) / 2) + 1; // multiply with *long* 3L to stay positive
		// If newSize is negative (happens when size become too large for
		// int), just increase the array by MIN_CAPACITY. This obviously
		// doesn't prevent a NegativeArraySizeException either, but it
		// postpones it to the moment when the int-sized array will be
		// completely full. At this point, nothing can be done except using
		// two MemIntStack instances which requires changes in the places
		// where MemIntStack is used or swapping MemIntStack to disk (which -
		// from looking at the ctor's parameters - appears to be the preferred
		// solution of the original MemIntStack authors).
		//
		// Performance obviously goes south the moment the array is 
		// increased in MIN_CAPACITY steps. It's a trade off between risking
		// an OutOfMemory exception and performance.
		return new int[Math.max(newSize, this.size + minCapacity)];
	}

	/**
	 * Return the number of items on the stack.
	 */
	public final long size() {
		return this.size;
	}

	public final boolean hasElements() {
		return this.size > 0;
	}
}
