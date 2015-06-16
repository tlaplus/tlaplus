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

package tlc2.value;

import junit.framework.TestCase;
import util.InternTable;
import util.UniqueString;

public class RecordValueTest extends TestCase {

	/**
	 * Test method for {@link tlc2.value.RecordValue#deepCopy()}.
	 * 
	 * This test reveals a bug in the implementation of RecordValue#deepCopy()
	 * when the original instance from which the deep copy has been created is
	 * normalized afterwards and the normalization incorrectly ripples through
	 * to the copy.
	 */
	public void testDeepCopy() {
		final InternTable internTable = new InternTable(2);
		final UniqueString a = internTable.put("a");
		final UniqueString b = internTable.put("b");
		
		final Value aVal = new StringValue("aVal");
		final Value bVal = new StringValue("bVal");
		
		// Create the source to create a deep copy of
		final RecordValue orig = new RecordValue(new UniqueString[] {b, a}, new Value[] {bVal, aVal}, false);
		
		// Verify the mappings in RecordValue are correct
		assertTrue(orig.names[0].equals(b));
		assertTrue(orig.names[1].equals(a));
		assertTrue(orig.values[0].equals(bVal));
		assertTrue(orig.values[1].equals(aVal));
		
		// Make a deep copy of te origina record value
		final RecordValue deepCopy = (RecordValue) orig.deepCopy();
		
		// Normalize the original record value and check its mappings have been
		// re-organized
		orig.deepNormalize();
		assertTrue(orig.names[0].equals(a));
		assertTrue(orig.names[1].equals(b));
		assertTrue(orig.values[0].equals(aVal));
		assertTrue(orig.values[1].equals(bVal));
		
		// Check that the mappings in the deep copy didn't change.
		assertTrue(deepCopy.names[0].equals(b));
		assertTrue(deepCopy.names[1].equals(a));
		assertTrue(deepCopy.values[0].equals(bVal));
		assertTrue(deepCopy.values[1].equals(aVal));
	}
}
