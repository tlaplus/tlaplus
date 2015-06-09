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

import java.io.File;

import junit.framework.TestCase;

public class SynchronousDiskIntStackTest extends TestCase {

	public void testPushIntNoWrite() {
		final String diskdir = System.getProperty("java.io.tmpdir") + File.separator + "SynchronousDiskIntStackTest_"
				+ System.currentTimeMillis();

		final int size = 8;
		
		final IntStack diskIntStack = new SynchronousDiskIntStack(diskdir, "SynchronousDiskIntStackTest", size);
		
		// Fill stack
		for (int i = 0; i < size; i++) {
			diskIntStack.pushInt(i);
		}

		// Check all elements still on stack
		for (int i = size - 1; i >= 0; i--) {
			assertEquals(i, diskIntStack.popInt());
		}
	}

	public void testPushIntWrite() {
		final String diskdir = System.getProperty("java.io.tmpdir") + File.separator + "SynchronousDiskIntStackTest_"
				+ System.currentTimeMillis();
		new File(diskdir).mkdirs();

		final int size = 8;
		
		final IntStack diskIntStack = new SynchronousDiskIntStack(diskdir, "SynchronousDiskIntStackTest", size);
		
		// Fill stack trice
		for (int i = 0; i < (size * 3); i++) {
			diskIntStack.pushInt(i);
		}

		// Check all elements still on stack
		for (int i = (3*size) - 1; i >= 0; i--) {
			assertEquals(i, diskIntStack.popInt());
		}
		
		assertEquals(0, diskIntStack.size());
	}
}
