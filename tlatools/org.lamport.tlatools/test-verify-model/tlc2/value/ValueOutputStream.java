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

import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Arrays;

import util.BufferedDataOutputStream;

/** JPF model of {@code ValueOutputStream} for pool files. */
public final class ValueOutputStream implements IValueOutputStream {

	private final String name;
	private long[] values = new long[8];
	private int count;
	private boolean closed;

	public ValueOutputStream(final File file) throws IOException {
		this.name = file.getPath();
		PoolFiles.openForWriting(this.name);
	}

	public ValueOutputStream(final File file, final boolean compress) throws IOException {
		this(file);
	}

	public ValueOutputStream(final OutputStream out, final boolean compress) throws IOException {
		throw new UnsupportedOperationException("A pool file is not modeled as a stream.");
	}

	public ValueOutputStream(final String fname) throws IOException {
		this(new File(fname));
	}

	public ValueOutputStream(final String fname, final boolean zip) throws IOException {
		this(new File(fname));
	}

	public final void writeShort(final short x) throws IOException {
		record(x);
	}

	public final void writeInt(final int x) throws IOException {
		record(x);
	}

	public final void writeLong(final long x) throws IOException {
		record(x);
	}

	public final void writeShortNat(final short x) throws IOException {
		record(x);
	}

	public final void writeNat(final int x) throws IOException {
		record(x);
	}

	public final void writeLongNat(final long x) throws IOException {
		record(x);
	}

	public final void writeByte(final byte b) throws IOException {
		record(b);
	}

	public final void writeBoolean(final boolean b) throws IOException {
		record(b ? 1 : 0);
	}

	public final void close() throws IOException {
		if (this.closed) {
			throw new IOException("Pool file " + this.name + " is already closed.");
		}
		this.closed = true;
		PoolFiles.commit(this.name, Arrays.copyOf(this.values, this.count));
	}

	public final BufferedDataOutputStream getOutputStream() {
		throw new UnsupportedOperationException("A pool file is not modeled as a stream.");
	}

	public final int put(final Object obj) {
		throw new UnsupportedOperationException(
				"Value de-duplication is not modeled; a state on the queue of a JPF harness has no values.");
	}

	private void record(final long value) throws IOException {
		if (this.closed) {
			throw new IOException("Pool file " + this.name + " is closed.");
		}
		if (this.count == this.values.length) {
			this.values = Arrays.copyOf(this.values, 2 * this.values.length);
		}
		this.values[this.count++] = value;
	}
}
