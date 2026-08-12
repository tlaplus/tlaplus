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

import java.util.List;
import java.util.stream.Collectors;

import org.junit.Assert;
import org.junit.Test;

import tla2sany.api.DependencyTable;
import tla2sany.api.Frontend;
import tla2sany.api.ModuleSyntaxTree;
import tla2sany.api.Resolver;
import tla2sany.api.SANYFrontend;
import tla2sany.api.StringResolver;
import tla2sany.parser.ParseException;
import tla2sany.semantic.Errors.ErrorDetails;

/**
 * Tests error handling for unresolved operators used with subexpression
 * selectors.
 */
public class TestSubexpressionSelectors {

	/**
	 * Runs SANY's syntax & semantic processing over a module body, returning the
	 * error log. An {@link AbortException} is swallowed so that the log can be
	 * inspected; it records the same error that caused the abort.
	 *
	 * @param moduleBody The lines to place between the module header & footer.
	 * @return The log of recorded messages.
	 */
	private static Errors process(final String moduleBody) throws ParseException {
		final String moduleName = "Test";
		final String module = "---- MODULE " + moduleName + " ----\n" + moduleBody + "\n====\n";
		final Frontend parser = new SANYFrontend();
		final Resolver resolver = new StringResolver(moduleName, module);
		final ModuleSyntaxTree syntaxTree = parser.processSyntax(moduleName, resolver);
		final Errors log = new Errors();
		try {
			final DependencyTable dependencies = parser.resolveDependencies(syntaxTree, resolver, log);
			parser.processSemantics(dependencies, log);
		} catch (AbortException e) {
			// The error causing the abort is in the log, which is checked below.
		}
		return log;
	}

	/**
	 * Asserts that the input was rejected, and that it was rejected with an error a
	 * user can act on rather than with an internal assertion failure.
	 *
	 * @param log The log of recorded messages.
	 */
	private static void assertRejectedWithUserFacingError(final Errors log) {
		Assert.assertTrue("Expected the input to be rejected", log.isFailure());
		final List<ErrorCode> internal = log.getErrorDetails().stream().map(ErrorDetails::getCode)
				.filter(code -> ErrorCode.INTERNAL_ERROR == code).collect(Collectors.toList());
		Assert.assertEquals(log.toString(), List.of(), internal);
	}

	/**
	 * Once lookup exhausts a compound operator name, the selector index points at
	 * its final segment. The diagnostic must name the complete unresolved operator,
	 * not just that segment.
	 */
	@Test
	public void testUnresolvedCompoundOperatorName() throws ParseException {
		final Errors log = process("use == module!op");
		assertRejectedWithUserFacingError(log);
		Assert.assertEquals(ErrorCode.SYMBOL_UNDEFINED, log.getErrorDetails().get(0).getCode());
		Assert.assertEquals("Unknown operator: `module!op'.", log.getErrorDetails().get(0).getMessage());
	}
}
