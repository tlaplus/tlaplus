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
import java.io.InputStream;

import util.IDataInputStream;
import util.UniqueString;

/** JPF model of {@code ValueInputStream} for pool files. */
public final class ValueInputStream implements IValueInputStream {

	private final String name;
	private final long[] values;
	private int index;
	private boolean closed;

	public ValueInputStream(final File file) throws IOException {
		this.name = file.getPath();
		this.values = PoolFiles.openForReading(this.name);
	}

	public ValueInputStream(final File file, final boolean compressed) throws IOException {
		this(file);
	}

	public ValueInputStream(final String fname) throws IOException {
		this(new File(fname));
	}

	public ValueInputStream(final InputStream in) throws IOException {
		throw new UnsupportedOperationException("A pool file is not modeled as a stream.");
	}

	public final int readShort() throws IOException {
		return (short) next();
	}

	public final int readInt() throws IOException {
		return (int) next();
	}

	public final long readLong() throws IOException {
		return next();
	}

	public final int readNat() throws IOException {
		return (int) next();
	}

	public final short readShortNat() throws IOException {
		return (short) next();
	}

	public final long readLongNat() throws IOException {
		return next();
	}

	public final byte readByte() throws IOException {
		return (byte) next();
	}

	public final void close() throws IOException {
		if (this.closed) {
			throw new IOException("Pool file " + this.name + " is already closed.");
		}
		this.closed = true;
		PoolFiles.closeForReading(this.name);
		if (this.index != this.values.length) {
			throw PoolFiles.violation("Read " + this.index + " of the " + this.values.length
					+ " values of pool file " + this.name + ", so the buffer that wrote it and the"
					+ " buffer reading it are not the same size.");
		}
	}

	public final IValue read() throws IOException {
		throw new UnsupportedOperationException(
				"A state on the queue of a JPF harness has no values to read.");
	}

	public final void assign(final Object obj, final int idx) {
		throw new UnsupportedOperationException("Value de-duplication is not modeled.");
	}

	public final int getIndex() {
		throw new UnsupportedOperationException("Value de-duplication is not modeled.");
	}

	public final UniqueString getValue(final int idx) {
		throw new UnsupportedOperationException("Value de-duplication is not modeled.");
	}

	public final IDataInputStream getInputStream() {
		throw new UnsupportedOperationException("A pool file is not modeled as a stream.");
	}

	private long next() throws IOException {
		if (this.closed) {
			throw new IOException("Pool file " + this.name + " is closed.");
		}
		if (this.index == this.values.length) {
			throw PoolFiles.violation("Pool file " + this.name + " holds " + this.values.length
					+ " values, so there is nothing left for this read, which means more states are"
					+ " being read back than were written.");
		}
		return this.values[this.index++];
	}
}
