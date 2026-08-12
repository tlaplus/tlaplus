/*******************************************************************************
 * Copyright (c) 2026 Linux Foundation. All rights reserved.
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

import java.util.Arrays;
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
 * Tests level checking of module instances.
 */
public class TestInstanceNode {

	/**
	 * When an INSTANCE substitutes an operator for an operator-valued module
	 * constant such as F(_, _), that operator must accept every argument level at
	 * which F is used. The diagnostic reports the one-based argument position and
	 * its required level, not the unrelated maximum level of F itself.
	 */
	@Test
	public void testOperatorArgumentMinimumLevelDiagnostic() throws ParseException, AbortException {
		final String moduleName = "Test";
		final String module = "---- MODULE Test ----\n"
				+ "---- MODULE Inner ----\n"
				+ "CONSTANT F(_, _)\n"
				+ "op == F([]TRUE, 0)\n"
				+ "====\n"
				+ "INSTANCE Inner WITH F <- =\n"
				+ "====\n";
		final Frontend parser = new SANYFrontend();
		final Resolver resolver = new StringResolver(moduleName, module);
		final ModuleSyntaxTree syntaxTree = parser.processSyntax(moduleName, resolver);
		final Errors semanticLog = new Errors();
		final DependencyTable dependencies = parser.resolveDependencies(syntaxTree, resolver, semanticLog);
		final ExternalModuleTable semanticTree = parser.processSemantics(dependencies, semanticLog);
		Assert.assertTrue(semanticLog.toString(), semanticLog.isSuccess());

		final Errors levelLog = new Errors();
		Assert.assertFalse(parser.checkLevel(semanticTree, levelLog));
		Assert.assertEquals(levelLog.toString(), 1, levelLog.getErrorDetails().size());
		final List<ErrorDetails> diagnostics = levelLog.getErrorDetails().stream()
				.filter(error -> error.getCode() == ErrorCode.INSTANCE_SUBSTITUTION_LEVEL_CONSTRAINT_NOT_MET)
				.collect(Collectors.toList());
		Assert.assertEquals(levelLog.toString(), 1, diagnostics.size());

		final List<Object> parameters = diagnostics.get(0).getParameters();
		// [1, 3] means that the first argument, []TRUE, requires temporal level
		// (3); it does not describe the levels of F's two arguments.
		Assert.assertEquals("The diagnostic should report a one-based argument position and its required level",
				Arrays.asList(1, 3), Arrays.asList(parameters.get(1), parameters.get(3)));
	}
}
