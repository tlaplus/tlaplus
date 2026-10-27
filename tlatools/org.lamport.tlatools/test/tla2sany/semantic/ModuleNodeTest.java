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

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

/**
 * Unit tests for the {@link ModuleNode} class.
 */
public class ModuleNodeTest {

  @Test
  public void testModuleNodeVariableDeclarationOrder() {
    final ContextTest ctxTest = new ContextTest();
    final ExternalModuleTable emt = new ExternalModuleTable();
    final Context ctx = Context.getGlobalContext().duplicate(emt);
    final List<OpDeclNode> expected = new ArrayList<>();
    for (int i = 0; i < 100; i++) {
      final OpDeclNode variable = ctxTest.mkVariable();
      ctx.addSymbolToContext(variable.getName(), variable);
      expected.add(variable);
    }

    ContextTest.assertIterableEqual(expected, ctx.getVariableDecls());
    final ModuleNode module = ctxTest.mkModule(ctx);
    final OpDeclNode[] actual = module.getVariableDecls();
    Assert.assertArrayEquals(expected.toArray(), actual);
  }

  @Test
  public void testModuleNodeConstantDeclarationOrder() {
    final ContextTest ctxTest = new ContextTest();
    final ExternalModuleTable emt = new ExternalModuleTable();
    final Context ctx = Context.getGlobalContext().duplicate(emt);
    final List<OpDeclNode> expected = new ArrayList<>();
    for (int i = 0; i < 100; i++) {
      final OpDeclNode constant = ctxTest.mkConstant();
      ctx.addSymbolToContext(constant.getName(), constant);
      expected.add(constant);
    }

    ContextTest.assertIterableEqual(expected, ctx.getConstantDecls());
    final ModuleNode module = ctxTest.mkModule(ctx);
    final OpDeclNode[] actual = module.getConstantDecls();
    Assert.assertArrayEquals(expected.toArray(), actual);
  }
}
