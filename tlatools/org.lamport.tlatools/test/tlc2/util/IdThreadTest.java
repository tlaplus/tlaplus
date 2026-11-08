/*******************************************************************************
 * Copyright (c) 2026 Matt Van Horn. All rights reserved.
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
 *   Matt Van Horn - initial API and implementation
 ******************************************************************************/
package tlc2.util;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNull;

import org.junit.Test;

import tlc2.value.impl.IntValue;

public class IdThreadTest {

	@Test
	public void testSetGetLocalValue() {
		final IdThread t = new IdThread(0);
		assertNull(t.getLocalValue(42));

		t.setLocalValue(1, IntValue.gen(1));
		t.setLocalValue(42, IntValue.gen(42));
		assertEquals(IntValue.gen(1), t.getLocalValue(1));
		assertEquals(IntValue.gen(42), t.getLocalValue(42));
		assertNull(t.getLocalValue(43));
	}
}
