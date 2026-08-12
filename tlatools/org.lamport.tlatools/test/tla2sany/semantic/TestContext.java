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

import org.junit.Assert;
import org.junit.Test;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.Errors.ErrorDetails;
import util.UniqueString;

/**
 * Tests merging symbol contexts.
 */
public class TestContext {

	/**
	 * A symbol imported by EXTENDS can conflict with an existing symbol of a
	 * different class. The diagnostic must identify the kind of each side of the
	 * conflict.
	 */
	@Test
	public void testDifferentSymbolClassesDiagnostic() {
		final UniqueString name = UniqueString.uniqueStringOf("symbol");
		final OpDefNode existingDefinition = new OpDefNode(name);
		final OpDeclNode incomingDeclaration = new OpDeclNode(name, ASTConstants.ConstantDeclKind,
				LevelConstants.ConstantLevel, 0, null, null, SyntaxTreeNode.nullSTN);
		final Context context = new Context(null);
		context.addSymbolToContext(name, existingDefinition);
		final Context incoming = new Context(null);
		incoming.addSymbolToContext(name, incomingDeclaration);
		final Errors log = new Errors();

		Assert.assertFalse(context.mergeExtendContext(incoming, log));
		Assert.assertEquals(log.toString(), 1, log.getErrorDetails().size());
		final ErrorDetails diagnostic = log.getErrorDetails().get(0);
		Assert.assertEquals(ErrorCode.EXTENDED_MODULES_SYMBOL_UNIFICATION_CONFLICT, diagnostic.getCode());

		final List<Object> parameters = diagnostic.getParameters();
		Assert.assertEquals("The diagnostic should identify the incoming and existing symbol kinds",
				Arrays.asList("declaration", "definition"), Arrays.asList(parameters.get(0), parameters.get(2)));
	}
}
