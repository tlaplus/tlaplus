/*******************************************************************************
 * Copyright (c) 2026 The Linux Foundation. All rights reserved.
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
 ******************************************************************************/
package tla2sany.output;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;

import org.junit.Assert;
import org.junit.Test;

import tla2sany.parser.TLAplusParser;

/**
 * {@link SanyOutput#log} interpolates its arguments into the given message with
 * {@link String#format}, but several callers pass text they assembled from the
 * spec being parsed as that message. Since TLA⁺'s grammar includes the % and %%
 * operators, such text can contain what looks like a format specifier - so a
 * message must be logged verbatim when the caller supplied no arguments to
 * interpolate.
 *
 * This is the same defect as the one tested by
 * {@link tla2sany.semantic.TestErrorMessageFormatting}, in the other place
 * where SANY renders messages.
 */
public class TestSanyOutputFormatting {

	/**
	 * Logs one message with no arguments and returns what was written.
	 *
	 * @param message The message to log.
	 * @return The logged output.
	 */
	private static String log(final String message) {
		final ByteArrayOutputStream out = new ByteArrayOutputStream();
		final SanyOutput log = new SimpleSanyOutput(new PrintStream(out, true, StandardCharsets.UTF_8), LogLevel.INFO);
		log.log(LogLevel.ERROR, message);
		return out.toString(StandardCharsets.UTF_8);
	}

	/**
	 * A percent sign in a message logged without arguments is not the start of a
	 * format specifier, whether or not it happens to form a valid one.
	 */
	@Test
	public void testPercentSignInMessageWithoutArguments() {
		Assert.assertEquals("Couldn't resolve infix operator symbol `%'." + System.lineSeparator(),
				log("Couldn't resolve infix operator symbol `%'."));
		Assert.assertEquals("Couldn't resolve infix operator symbol `%%'." + System.lineSeparator(),
				log("Couldn't resolve infix operator symbol `%%'."));
	}

	/**
	 * Callers that do supply arguments still get them interpolated.
	 */
	@Test
	public void testArgumentsAreStillInterpolated() {
		final ByteArrayOutputStream out = new ByteArrayOutputStream();
		final SanyOutput log = new SimpleSanyOutput(new PrintStream(out, true, StandardCharsets.UTF_8), LogLevel.INFO);
		log.log(LogLevel.ERROR, "Parsing module %s in file %s", "Test", "Test.tla");
		Assert.assertEquals("Parsing module Test in file Test.tla" + System.lineSeparator(),
				out.toString(StandardCharsets.UTF_8));
	}

	/**
	 * The parser reports its errors by passing them to {@link SanyOutput#log} as
	 * the message, so a spec whose parse error has to mention the % operator must
	 * still get its error reported.
	 */
	@Test
	public void testParseErrorMentioningPercentOperator() {
		final String module = "---- MODULE Test ----\nop == % 1\n====\n";
		final ByteArrayOutputStream out = new ByteArrayOutputStream();
		final SanyOutput log = new SimpleSanyOutput(new PrintStream(out, true, StandardCharsets.UTF_8), LogLevel.INFO);
		final TLAplusParser parser = new TLAplusParser(log, module.getBytes(StandardCharsets.UTF_8));
		Assert.assertFalse(parser.parse());
		final String actual = out.toString(StandardCharsets.UTF_8);
		Assert.assertTrue(actual, actual.contains("token \"%\""));
	}
}
