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
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.jcstress;

import tlc2.util.FP64;
import tlc2.value.impl.EnumerableValue;
import tlc2.value.impl.SetEnumValue;

/**
 * The two workers of the lazy-set tests, which start from an empty cache. One
 * worker fingerprints the set, which fills the cache, while another reads the
 * cache. If fingerprinting publishes the cache without a lock or volatile, the
 * reader may see the cache but, because SetEnumValue#elems isn't final, elems
 * as null (-1) or as an empty ValueVec. TLC as of 425dc60aa did so, although
 * its lifecycle (#361) assumes that workers never fill the cache of a shared
 * value. It also built the cache in one synchronized block and published it in
 * another, and read it without a lock, so that the reader could see elems as
 * stale.
 * <p>
 * The operands of the sets are sorted, so that enumerating them doesn't sort
 * them in place, which is the race of #1445, not of #439.
 * 
 * @see https://github.com/tlaplus/tlaplus/issues/439
 */
final class LazySets {

	static {
		FP64.Init();
	}

	/** Fills the cache of set, and returns 1. */
	static int publish(final EnumerableValue set) {
		return Codes.catching(() -> {
			set.fingerPrint(FP64.New());
			return 1;
		});
	}

	/** Returns the number of elements of the cache of set, if set has one. */
	static int read(final EnumerableValue set) {
		return Codes.catching(() -> ((SetEnumValue) set.toSetEnum()).elems.size());
	}
}
