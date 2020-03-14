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

package tlc2.model;

import static org.junit.Assert.assertEquals;

import org.junit.Test;

import tlc2.model.Assignment;

public class AssignmentTest {

	@Test
	public void test() {
		final Assignment a = new Assignment("X", new String[0], "X");
		a.setModelValue(true);
		assertEquals("X", a.prettyPrint());
		
		final Assignment b = new Assignment("Y", new String[0], "{a1, b1}");
		b.setModelValue(true);
		assertEquals("Y" + Assignment.ASSIGNMENT_SIGN + "{a1, b1}", b.prettyPrint());

		final Assignment c = new Assignment("Z", new String[0], "{s1, s2}");
		c.setModelValue(true);
		c.setSymmetric(true);
		assertEquals("Z" + Assignment.ASSIGNMENT_SIGN + "s{s1, s2}", c.prettyPrint());

		final Assignment d = new Assignment("W", new String[0], "1");
		assertEquals("W" + Assignment.ASSIGNMENT_SIGN + "1", d.prettyPrint());
	}
}
