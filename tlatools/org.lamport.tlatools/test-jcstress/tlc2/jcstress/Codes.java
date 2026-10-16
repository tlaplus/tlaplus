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

import java.util.function.IntSupplier;

import tlc2.tool.EvalException;

/** Encodes the exception a worker throws as a negative result. */
final class Codes {

	/** Explains the negative results in the description of an outcome. */
	static final String LEGEND = "(-1 NPE, -2 TLC error, -3 AIOOBE, -4 CCE, -9 other)";

	/** The result of the worker, or the code of the exception it throws. */
	static int catching(final IntSupplier worker) {
		try {
			return worker.getAsInt();
		} catch (Throwable e) {
			return of(e);
		}
	}

	static int of(Throwable e) {
		Throwable t = e;
		while (t.getCause() != null && t.getCause() != t) {
			t = t.getCause();
		}
		if (t instanceof NullPointerException) {
			return -1;
		}
		if (t instanceof EvalException || t.getClass().getName().startsWith("tlc2.")) {
			return -2; // e.g. Assert.fail("... not in the domain of the function.")
		}
		if (t instanceof ArrayIndexOutOfBoundsException) {
			return -3;
		}
		if (t instanceof ClassCastException) {
			return -4;
		}
		return -9;
	}
}
