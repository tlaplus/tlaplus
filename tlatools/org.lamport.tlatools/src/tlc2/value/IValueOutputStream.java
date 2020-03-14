/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
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

import java.io.IOException;

import util.IDataOutputStream;

public interface IValueOutputStream {

	void writeShort(short x) throws IOException;

	void writeInt(int x) throws IOException;

	void writeLong(long x) throws IOException;

	void close() throws IOException;

	/* Precondition: x is a non-negative short. */
	void writeShortNat(short x) throws IOException;

	/* Precondition: x is a non-negative int. */
	void writeNat(int x) throws IOException;

	/* Precondition: x is a non-negative long. */
	void writeLongNat(long x) throws IOException;

	void writeByte(byte b) throws IOException;

	void writeBoolean(boolean b) throws IOException;

	IDataOutputStream getOutputStream();

	/**
	 * Check if another TLCState - which is currently also being serialized to the
	 * same storage (i.e. disk file) - has/contains an identical Value. If yes, do
	 * not serialize the Value instance again but make this TLCState point to the
	 * Value instance previously serialized for the other TLCState. In other words,
	 * this is a custom-tailored compression/de-duplication mechanism for Value
	 * instances.
	 * <p>
	 * This approach only works because both TLCStates are serialized to the same
	 * storage and thus de-serialized as part of the same operation (same
	 * Value*Stream instance).
	 * <p>
	 * The purpose of this approach appears to be:
	 * <ul>
	 * <li>Reduce serialization efforts and storage size</li>
	 * <li>Reduce the number of Value instances created during de-serialization</li>
	 * <li>Allow identity comparison on Value instances (AFAICT not used by Value
	 * explicitly, just UniqueString) to speed up check. Value#equals internally
	 * likely uses identity comparison as first check.</li>
	 * </ul>
	 * <p>
	 * A disadvantage is the cost of maintaining the internal HandleTable which can
	 * grow to thousands of elements during serialization/de-serialization (in
	 * ValueInputStream). Since serialization suspends the DiskStateQueue and thus
	 * blocks tlc2.tool.Workers from exploring the state space, this might has
	 * adverse effects.
	 */
	int put(Object obj);

}