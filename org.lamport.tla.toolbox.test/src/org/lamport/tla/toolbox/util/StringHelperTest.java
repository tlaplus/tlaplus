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

package org.lamport.tla.toolbox.util;

import static org.junit.Assert.assertArrayEquals;
import junit.framework.TestCase;

public class StringHelperTest extends TestCase {

	public void testGetWords() {
		String[] words = StringHelper.getWords("Abc def ghi.");
		assertArrayEquals(new String[]{"Abc", "def", "ghi."}, words);

		words = StringHelper.getWords("Abc  def    ghi.      ");
		assertArrayEquals(new String[]{"Abc", "def", "ghi."}, words);
	}
	public void testGetWordsLeadingSpace() {
		String[] words = StringHelper.getWords("     Abc def ghi.");
		assertArrayEquals(new String[]{"Abc", "def", "ghi."}, words);
	}
//TODO What is the intended behavior here?
//	public void testGetWordsEmpty() {
//		String[] words = StringHelper.getWords("");
//		assertArrayEquals(new String[0], words);
//	}
	public void testGetWordsNull() {
		try {
			StringHelper.getWords(null);
		} catch (NullPointerException e) {
			return;
		}
		fail("null should not be accepted!");
	}
	
	public void testCopyString0() {
		String copyString = StringHelper.copyString("abc", 0);
		assertEquals("", copyString);
	}
	public void testCopyStringPos1() {
		String copyString = StringHelper.copyString("abc", 1);
		assertEquals("abc", copyString);
	}
	public void testCopyStringPos5() {
		String copyString = StringHelper.copyString("abc", 5);
		assertEquals("abcabcabcabcabc", copyString);
	}
	public void testCopyStringNeg1() {
		String copyString = StringHelper.copyString("abc", -1);
		assertEquals("", copyString);
	}
	public void testCopyStringNeg5() {
		String copyString = StringHelper.copyString("abc", -5);
		assertEquals("", copyString);
	}
//TODO What is the intended behavior of passing a null string?
//	public void testCopyStringNullPos() {
//		try {
//			StringHelper.copyString(null, 1);
//		} catch (NullPointerException e) {
//			return;
//		}
//		fail("null should not be accepted!");
//	}
//TODO What is the intended behavior of passing a null string?
//	public void testCopyStringNullNeg() {
//		try {
//			StringHelper.copyString(null, -1);
//		} catch (NullPointerException e) {
//			return;
//		}
//		fail("null should not be accepted!");
//	}
	
	public void testOnlySpaces() {
		assertTrue(StringHelper.onlySpaces("        "));
		assertTrue(StringHelper.onlySpaces(" "));
		assertFalse(StringHelper.onlySpaces("  a  "));
		assertFalse(StringHelper.onlySpaces(" a"));
		assertFalse(StringHelper.onlySpaces("a "));
		assertFalse(StringHelper.onlySpaces("a"));
	}
	public void testOnlySpacesNull() {
		try {
			StringHelper.onlySpaces(null);
		} catch (NullPointerException e) {
			return;
		}
		fail("null should not be accepted!");
	}
//TODO What is the intended behavior for the empty string?
//	public void testOnlySpacesEmptyString() {
//		assertFalse(StringHelper.onlySpaces(""));
//	}
	
	public void testTrimFront() {
		assertEquals("", StringHelper.trimFront("    "));
		assertEquals("a", StringHelper.trimFront(" a"));
		assertEquals("a ", StringHelper.trimFront(" a "));
		assertEquals("aaa", StringHelper.trimFront(" aaa"));
		assertEquals("aa", StringHelper.trimFront("  aa"));
		assertEquals("a ", StringHelper.trimFront("   a "));
		assertEquals("aa  a ", StringHelper.trimFront("  aa  a "));
	}
	public void testTrimFrontNull() {
		try {
			StringHelper.trimFront(null);
		} catch (NullPointerException e) {
			return;
		}
		fail("null should not be accepted!");
	}
	public void testTrimFrontWhitespaces() {
		assertEquals("Abc def ghi.", StringHelper.trimFront("Abc def ghi."));
	}

	public void testTrimEnd() {
		assertEquals("", StringHelper.trimEnd("    "));
		assertEquals("a", StringHelper.trimEnd("a "));
		assertEquals(" a", StringHelper.trimEnd(" a "));
		assertEquals("aaa", StringHelper.trimEnd("aaa   "));
		assertEquals("aa", StringHelper.trimEnd("aa  "));
		assertEquals(" a", StringHelper.trimEnd(" a  "));
		assertEquals(" a aa", StringHelper.trimEnd(" a aa "));
	}
	public void testTrimEndNull() {
		try {
			StringHelper.trimEnd(null);
		} catch (NullPointerException e) {
			return;
		}
		fail("null should not be accepted!");
	}
	public void testTrimEndWhitespaces() {
		assertEquals("Abc def ghi.", StringHelper.trimEnd("Abc def ghi."));
	}
	
	public void testLeadingSpace() {
		assertEquals(1, StringHelper.leadingSpaces(" "));
		assertEquals(2, StringHelper.leadingSpaces("  "));
		assertEquals(1, StringHelper.leadingSpaces(" a "));
		assertEquals(2, StringHelper.leadingSpaces("  a  a  "));
		assertEquals(0, StringHelper.leadingSpaces("a"));
	}
	public void testLeadingSpacesNull() {
		try {
			StringHelper.leadingSpaces(null);
		} catch (NullPointerException e) {
			return;
		}
		fail("null should not be accepted!");
	}
	
	public void testIsIdentifier() {
		assertFalse(StringHelper.isIdentifier("123"));
		assertFalse(StringHelper.isIdentifier(" 123"));
		assertFalse(StringHelper.isIdentifier("123 "));
		assertFalse(StringHelper.isIdentifier(" 123 "));
		assertTrue(StringHelper.isIdentifier("1A1"));
		assertTrue(StringHelper.isIdentifier("_1"));
		assertTrue(StringHelper.isIdentifier("1_"));
		assertTrue(StringHelper.isIdentifier("_"));
	}
	public void testIsIdentifierNull() {
		try {
			StringHelper.isIdentifier(null);
		} catch (NullPointerException e) {
			return;
		}
		fail("null should not be accepted!");
	}
//TODO What is the intended behavior for the empty string?
//	public void testIsIdentifierMetaChars() {
//		assertTrue(StringHelper.isIdentifier("\\"));
//	}
//TODO What is the intended behavior for the empty string?
//	public void testIsIdentifierEmptyString() {
//		assertTrue(StringHelper.isIdentifier(""));
//	}
}
