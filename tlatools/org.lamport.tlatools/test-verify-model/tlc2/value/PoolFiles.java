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
package tlc2.value;

import java.util.HashMap;
import java.util.Map;

/** Backtrackable in-memory pool files for JPF. */
final class PoolFiles {

	/** An Error so the pool threads cannot swallow model violations. */
	static final class Violation extends Error {
		private static final long serialVersionUID = 1L;

		private Violation(final String message) {
			super(message);
		}
	}

	private static final Map<String, Pool> POOLS = new HashMap<>();

	private static final class Pool {
		private long[] values;
		private boolean writing;
		private int readers;
	}

	static synchronized void openForWriting(final String name) {
		final Pool pool = pool(name);
		if (pool.writing) {
			throw new Violation("Pool file " + name + " is already open for writing, so two threads"
					+ " are writing the same pool file.");
		}
		if (pool.readers > 0) {
			throw new Violation("Pool file " + name + " is open for reading, so writing it now is the"
					+ " read-write conflict on a file that StatePoolWriter.ensureWritten exists to"
					+ " prevent.");
		}
		pool.writing = true;
	}

	static synchronized void commit(final String name, final long[] values) {
		final Pool pool = pool(name);
		pool.values = values;
		pool.writing = false;
	}

	static synchronized long[] openForReading(final String name) {
		final Pool pool = pool(name);
		if (pool.writing) {
			throw new Violation("Pool file " + name + " is open for writing, so reading it now is the"
					+ " read-write conflict on a file that StatePoolWriter.ensureWritten exists to"
					+ " prevent.");
		}
		if (pool.values == null) {
			throw new Violation("Pool file " + name + " has never been written, so the queue is"
					+ " reading a pool file that does not exist.");
		}
		pool.readers++;
		return pool.values.clone();
	}

	static synchronized void closeForReading(final String name) {
		pool(name).readers--;
	}

	static Violation violation(final String message) {
		return new Violation(message);
	}

	private static Pool pool(final String name) {
		Pool pool = POOLS.get(name);
		if (pool == null) {
			pool = new Pool();
			POOLS.put(name, pool);
		}
		return pool;
	}

	private PoolFiles() {
	}
}
