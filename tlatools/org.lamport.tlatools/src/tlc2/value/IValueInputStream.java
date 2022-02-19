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

import java.io.EOFException;
import java.io.IOException;

import util.IDataInputStream;

public interface IValueInputStream {

	IValue read() throws IOException;

	int readShort() throws IOException;
	
	default String readStringVal() throws IOException {
		IDataInputStream s = getInputStream();
		s.readInt();
		s.readInt();
		return s.readString(s.readInt());
	}

	int readInt() throws IOException;

	long readLong() throws IOException;

	void close() throws IOException;

	int readNat() throws IOException;

	short readShortNat() throws IOException;

	long readLongNat() throws IOException;

	byte readByte() throws EOFException, IOException;

	void assign(Object obj, int idx);

	int getIndex();

	IDataInputStream getInputStream();

	// TODO this is only used in RecordValue.createFrom()
	// it should either be purged or have its return type changed to either Object (or (I)Value)
	// the current state of having random objects in IValueStreams seems abusive.
	String getValue(int idx);
}