/*******************************************************************************
 * Copyright (c) 2017 Microsoft Research. All rights reserved. 
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
package util;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

public class TestPrintStream extends PrintStream {

	private final StringBuffer buf = new StringBuffer();
	private final List<String> strings = new ArrayList<String>();
	
	public TestPrintStream() {
        super(ToolIO.out);
	}

	/* (non-Javadoc)
	 * @see java.io.PrintStream#println(java.lang.String)
	 */
	public void println(String x) {
		strings.add(x);
		buf.append(x + "\n");
		super.println(x);
	}
	
	public void assertEmpty() {
		assertTrue(this.strings.isEmpty());
	}
	
	public void assertContains(final String seq) {
		assertTrue(buf.toString().contains(seq));
	}
	
	public void assertSubstring(String substring) {
		for (String string : strings) {
			if (string.contains(substring)) {
				return;
			}
		}
		fail("Substring not found");
	}

	public void assertRegex(String regex) {
		Pattern pattern = Pattern.compile(regex);
		for (String string : strings) {			
			if (pattern.matcher(string).find()) {
				return;
			}
		}
		fail("Match not found for regex \"" + pattern.toString() + "\"");		
	}
	
	public void assertNoSubstring(String substring) {
		for (String string : strings) {
			if (string.contains(substring)) {
				fail("Substring was found");
			}
		}
	}
}