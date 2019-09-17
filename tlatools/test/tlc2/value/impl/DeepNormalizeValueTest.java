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
package tlc2.value.impl;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class DeepNormalizeValueTest {
	
	/**
	 * Test method for {@link tlc2.value.impl.UnionValue#deepNormalize()}.
	 */
	@Test
	public void uv() {
		final ValueVec vec = new ValueVec();
		vec.addElement(new SetEnumValue(new IntValue[] {IntValue.gen(42)}, false));
		vec.addElement(new SetEnumValue(new IntValue[] {IntValue.gen(23)}, false));
		vec.addElement(new SetEnumValue(new IntValue[] {IntValue.gen(4711)}, false));
		vec.addElement(new SetEnumValue(new IntValue[] {IntValue.gen(1)}, false));
		
		final UnionValue uv = new UnionValue(new SetEnumValue(vec, false));
		assertFalse(uv.isNormalized());
		assertFalse(uv.set.isNormalized());
		
		uv.deepNormalize();
		
		assertTrue(uv.set.isNormalized());
	}
}
