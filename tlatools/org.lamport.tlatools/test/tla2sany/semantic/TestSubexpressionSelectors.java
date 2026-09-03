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
 * Subexpression selectors like op!&lt;&lt;!&gt;&gt; navigate into the parse
 * tree of the operator they are applied to. When the operator itself cannot be
 * resolved, SANY has nothing to navigate into and should report an ordinary
 * unresolved-symbol error. Instead, two or more consecutive non-name selectors
 * following an unresolved name make {@link Generator#selectorToNode} reach an
 * {@link ErrorCode#INTERNAL_ERROR} check ("Internal error: should have name
 * here.") and abort the parse. That error code is documented as being reserved
 * for assertions about SANY's own state, so reaching it from a syntactically
 * valid spec is a bug.
 *
 * These reproducers were found while running the standardized TLA⁺ syntax
 * corpus (also present in test/tla2sany/corpus) through SANY as part of the
 * work to use SANY as TLAPM's parser backend; see
 * https://github.com/tlaplus/tlapm/pull/275#issuecomment-5241074153
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

	/**
	 * The minimal form of the bug: an unresolved operator name followed by the two
	 * tree navigation selectors !&lt;&lt; and !&gt;&gt;. Removing either selector
	 * produces the expected "Unknown operator" error instead.
	 */
	@Test
	public void testConsecutiveTreeNavigationSelectors() throws ParseException {
		final Errors log = process("tree_nav == op!<<!>>");
		assertRejectedWithUserFacingError(log);
		Assert.assertEquals(ErrorCode.SYMBOL_UNDEFINED, log.getErrorDetails().get(0).getCode());
		Assert.assertEquals("Unknown operator: `op'.", log.getErrorDetails().get(0).getMessage());
	}

	/**
	 * The form found in the syntax corpus, exercising every kind of subexpression
	 * tree navigation selector at once. See the "Subexpression Tree Navigation"
	 * test in test/tla2sany/corpus/subexpressions.txt.
	 */
	@Test
	public void testAllTreeNavigationSelectors() throws ParseException {
		assertRejectedWithUserFacingError(process("tree_nav == op(a, b)!<<!>>!3!(x, y)!:!@"));
	}
}
