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
package tla2unicode;

import static org.junit.Assert.assertEquals;

import org.junit.Ignore;
import org.junit.Test;

// Tries to convert syntactically incorrect Unicode TLA+ into Ascii. This functionality 
// is needed to convert a Unicode spec into Ascii before it is passed to SANY for regular parsing.
public class UnicodeToAsciiTest {

	@Test
	public void testDanglingOpenMultiLine() {
		final String input = "----- MODULE test -----\n" + "(*\n" + "Foo ≜ TRUE\n=========\n";
		assertEquals(input.replace("≜", "=="), TLAUnicode.convert(false, input));
	}

	@Test
	public void testDanglingCloseMultiLine() {
		final String input = "----- MODULE test -----\n" + "*)\n" + "Foo ≜ TRUE\n=========\n";
		assertEquals(input.replace("≜", "=="), TLAUnicode.convert(false, input));
	}
	
	// TODO testRedundantOpenMultiLine is how TLAUnicode.covert should ideally
	// behave.
	@Test
	@Ignore
	public void testRedundantSingleLine() {
		final String input = "----- MODULE test -----\nBar ≜ TRUE\n" + "\\*\\* CommentString\n" + "Foo ≜ TRUE\n=========\n";
		assertEquals(input.replace("≜", "=="), TLAUnicode.convert(false, input));
	}

	@Test
	public void testRedundantSingleLineBestEffort() {
		final String input = "----- MODULE test -----\nBar ≜ TRUE\n" + "\\*\\* CommentString\n" + "Foo ≜ TRUE\n=========\n";
		assertEquals(input.replace("≜", "==").replace("\\* CommentString", ""), TLAUnicode.convert(false, input));
	}
	
	// TODO testRedundantOpenMultiLine is how TLAUnicode.covert should ideally
	// behave. However, I could only convince TokenizeSpec to return parts of the
	// input which I consider good enough for now.
	@Test
	public void testRedundantOpenMultiLineBestEffort() {
		final String input = "----- MODULE test -----\nBar ≜ TRUE\n" + "(*(* CommentString *)\n" + "Foo ≜ TRUE\n=========\n";
		assertEquals(input.replace("≜", "==").replace("(* CommentString *)", ""), TLAUnicode.convert(false, input));
	}
	
	@Test
	@Ignore
	public void testRedundantOpenMultiLine() {
		final String input = "----- MODULE test -----\nBar ≜ TRUE\n" + "(*(* CommentString *)\n" + "Foo ≜ TRUE\n=========\n";
		assertEquals(input.replace("≜", "=="), TLAUnicode.convert(false, input));
	}

	@Test
	@Ignore
	public void testRedundantOpenMultiLineAdditionalLevel() {
		final String input = "----- MODULE test -----\nBar ≜ TRUE\n" + "(*(*(* CommentString *)*)\n" + "Foo ≜ TRUE\n=========\n";
		assertEquals(input.replace("≜", "=="), TLAUnicode.convert(false, input));
	}

	@Test
	public void testRedundantCloseMultiLine() {
		final String input = "----- MODULE test -----\nBar ≜ TRUE\n" + "(**)*)\n" + "Foo ≜ TRUE\n=========\n";
		assertEquals(input.replace("≜", "=="), TLAUnicode.convert(false, input));
	}

	@Test
	public void testIllegalLexem() {
		final String input = "----- MODULE test -----\n" + "ööö" + "\nFoo ≜ TRUE\n===========\n";
		assertEquals(input.replace("≜", "=="), TLAUnicode.convert(false, input));
	}

	@Test
	public void testIllegalLexemInString() {
		final String input = "----- MODULE test -----\nFoo ≜ \"aaa" + "ööö" + "123\"\n===========\n";
		assertEquals(TLAUnicode.convert(false, input), input.replace("≜", "=="), TLAUnicode.convert(false, input));
	}

	@Test
	public void testNoEndOfModule() {
		final String input = "----- MODULE test -----\nFoo ≜ TRUE\n\n";
		assertEquals(input.replace("≜", "=="), TLAUnicode.convert(false, input));
	}
}
