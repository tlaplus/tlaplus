/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.value.impl;

/**
 * Common helpers for bounded JBMC value harnesses.
 */
public abstract class ValueHarness {
	protected static boolean isInt(final Value value, final int expected) {
		return value instanceof IntValue && ((IntValue) value).val == expected;
	}

	// Limit cardinality, not absolute endpoints, so each harness still checks
	// intervals adjacent to Integer.MIN_VALUE and Integer.MAX_VALUE.
	protected static int smallSize(final int low, final int high, final int maxSize) {
		final long size = cardinality(low, high);
		return size <= maxSize ? (int) size : -1;
	}

	protected static long cardinality(final int low, final int high) {
		return high < low ? 0L : (long) high - (long) low + 1L;
	}
}
