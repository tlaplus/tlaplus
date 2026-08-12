/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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
package tla2sany.semantic;

import org.junit.Assert;
import org.junit.Test;

import tla2sany.api.DependencyTable;
import tla2sany.api.Frontend;
import tla2sany.api.ModuleSyntaxTree;
import tla2sany.api.Resolver;
import tla2sany.api.SANYFrontend;
import tla2sany.api.StringResolver;
import tla2sany.parser.ParseException;
import tla2sany.st.Location;

/**
 * {@link Errors.ErrorDetails#getMessage()} renders a recorded message by
 * passing it to {@link String#format} whenever the call site supplied
 * parameters. Call sites therefore have to keep symbol names taken from the
 * spec out of the format string: TLA⁺'s grammar includes the infix operators %
 * and %%, so a symbol name can look like a format specifier and thereby either
 * crash the parser with {@link java.util.UnknownFormatConversionException} or
 * silently corrupt the message it is shown. Names passed as parameters are safe
 * because {@link String#format} does not scan its arguments, and messages
 * recorded without any parameters are safe because they are rendered verbatim.
 *
 * These reproducers were found while running the standardized TLA⁺ syntax
 * corpus (also present in test/tla2sany/corpus) through SANY as part of the
 * work to use SANY as TLAPM's parser backend; see
 * https://github.com/tlaplus/tlapm/pull/275#issuecomment-5241074153
 */
public class TestErrorMessageFormatting {

	/**
	 * Runs SANY's syntax & semantic processing over a module body, returning the
	 * error log. Semantic errors are non-fatal here so no exception is expected
	 * from any of the inputs below.
	 *
	 * @param moduleBody The lines to place between the module header & footer.
	 * @return The log of recorded messages, un-rendered.
	 */
	private static Errors process(final String moduleBody) throws ParseException, AbortException {
		final String moduleName = "Test";
		final String module = "---- MODULE " + moduleName + " ----\n" + moduleBody + "\n====\n";
		final Frontend parser = new SANYFrontend();
		final Resolver resolver = new StringResolver(moduleName, module);
		final ModuleSyntaxTree syntaxTree = parser.processSyntax(moduleName, resolver);
		final Errors log = new Errors();
		final DependencyTable dependencies = parser.resolveDependencies(syntaxTree, resolver, log);
		parser.processSemantics(dependencies, log);
		return log;
	}

	/**
	 * Asserts that at least one recorded error renders to a message containing the
	 * given substring. Rendering the log is the operation that crashes when a
	 * message contains a percent sign.
	 *
	 * @param log      The log of recorded messages.
	 * @param expected A substring expected in one of the rendered messages.
	 */
	private static void assertErrorContains(final Errors log, final String expected) {
		boolean found = false;
		final StringBuilder rendered = new StringBuilder();
		for (final String error : log.getErrors()) {
			rendered.append(error).append('\n');
			found |= error.contains(expected);
		}
		Assert.assertTrue("No error mentions " + expected + "; got:\n" + rendered, found);
	}

	/**
	 * The {@link Errors} class should record and return message text verbatim; the
	 * text is not written by the user of the parser and so cannot be expected to
	 * escape percent signs.
	 */
	@Test
	public void testPercentSignInMessageTextIsNotAFormatSpecifier() {
		final Errors log = new Errors();
		final String message = "Couldn't resolve infix operator symbol `%'.";
		log.addMessage(ErrorCode.SUSPECTED_UNREACHABLE_CHECK, Location.nullLoc, message);
		Assert.assertEquals(message, log.getErrorDetails().get(0).getMessage());
	}

	/**
	 * A symbol name interpolated into a message is passed as a parameter, so it
	 * reaches the rendered message unchanged no matter which operators it names.
	 */
	@Test
	public void testPercentSignInMessageParameterIsNotAFormatSpecifier() {
		final Errors log = new Errors();
		log.addMessage(ErrorCode.SUSPECTED_UNREACHABLE_CHECK, Location.nullLoc,
				"Couldn't resolve infix operator symbol `%s'.", "%%");
		Assert.assertEquals("Couldn't resolve infix operator symbol `%%'.", log.getErrorDetails().get(0).getMessage());
	}

	/**
	 * The % operator is defined in the Naturals standard module, so using it
	 * without extending Naturals is an ordinary unresolved-symbol error. SANY
	 * reports it by concatenating the symbol name into the message text, which
	 * yields the invalid format specifier "%'".
	 */
	@Test
	public void testUnresolvedPercentOperator() throws ParseException, AbortException {
		final Errors log = process("op == x % y");
		assertErrorContains(log, "%");
	}

	/**
	 * As above, but reaching a different message: the % operator used in nonfix
	 * form under a qualified name.
	 */
	@Test
	public void testUnresolvedNonfixPercentOperator() throws ParseException, AbortException {
		final Errors log = process("op == A!B!%(x, y)");
		assertErrorContains(log, "%");
	}

	/**
	 * The %% operator is not defined by any standard module, so it is always
	 * unresolved unless the spec defines it. Its name forms the valid format
	 * specifier "%%", which renders as a single percent sign, so instead of
	 * crashing SANY silently reports an error about the operator % rather than the
	 * operator %% that the spec actually mentions.
	 */
	@Test
	public void testUnresolvedDoublePercentOperatorIsNotRenamed() throws ParseException, AbortException {
		final Errors log = process("op == x %% y");
		assertErrorContains(log, "%%");
	}
}
