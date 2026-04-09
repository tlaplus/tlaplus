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

import org.junit.Test;

import util.UniqueString;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;

/**
 * Tests for the {@link Context} class, which along with {@link SymbolTable}
 * is responsible for tracking which definitions are in scope.
 */
public class ContextTest {

  private int seed = 0;

  UniqueString mkName(final String base) {
    return UniqueString.of(base + Integer.toString(this.seed++));
  }

  OpDefNode mkOpDef() {
    return new OpDefNode(mkName("op"), ASTConstants.UserDefinedOpKind, null, false, null, null, null, null, true, null);
  }

  OpDefNode mkInstance() {
    return new OpDefNode(mkName("instance"), ASTConstants.ModuleInstanceKind, null, false, null, null, null, null, true, null);
  }

  ModuleNode mkModule(final Context ctx) {
    return new ModuleNode(mkName("module"), ctx, null);
  }

  OpDeclNode mkVariable() {
    return new OpDeclNode(mkName("var"), ASTConstants.VariableDeclKind, 0, 0, null, null, null);
  }

  OpDeclNode mkConstant() {
    return new OpDeclNode(mkName("const"), ASTConstants.ConstantDeclKind, 0, 0, null, null, null);
  }

  ThmOrAssumpDefNode mkTheorem() {
    return new ThmOrAssumpDefNode(mkName("thm"), true, null, null, null, null, null, null, null);
  }

  ThmOrAssumpDefNode mkAssumption() {
    return new ThmOrAssumpDefNode(mkName("asm"), false, null, null, null, null, null, null, null);
  }

  static <T> void assertContentsEqual(List<T> expected, Iterable<Context.Pair> actual, boolean skipBuiltins) {
    int i = 0;
    for (final Context.Pair entry : actual) {
      if (skipBuiltins && entry.getSymbol().getKind() == ASTConstants.BuiltInKind) {
      } else {
        Assert.assertEquals(expected.get(i), entry.getSymbol());
        i++;
      }
    }
    Assert.assertEquals(expected.size(), i);
  }

  static <T> void assertIterableEqual(List<T> expected, Iterable<T> actual) {
    int i = 0;
    for (final T symbol : actual) {
      Assert.assertEquals(expected.get(i), symbol);
      i++;
    }
    Assert.assertEquals(expected.size(), i);
  }

  static <T> void assertReversedIterableEqual(List<T> expected, Iterable<T> actual) {
    int i = expected.size();
    for (final T symbol : actual) {
      Assert.assertEquals(expected.get(i - 1), symbol);
      i--;
    }
    Assert.assertEquals(0, i);
  }

  @Test
  public void testGlobalContextContainsBuiltInOperatorsInOrder() {
    int i = 0;
    for (final Context.Pair entry : Context.getGlobalContext().content()) {
      Assert.assertEquals(BuiltInOperators.Properties[i].Name, entry.getSymbol().getName());
      Assert.assertEquals(ASTConstants.BuiltInKind, entry.getSymbol().getKind());
      Assert.assertTrue(Context.isBuiltIn(entry.getSymbol()));
      Assert.assertTrue(Context.getGlobalContext().occurSymbol(entry.getSymbol().getName()));
      Assert.assertEquals(entry.getSymbol(), Context.getGlobalContext().getSymbol(entry.getSymbol().getName()));
      i++;
    }

    Assert.assertEquals(BuiltInOperators.Properties.length, i);
    Assert.assertEquals(0, Context.getGlobalContext().getOpDefs().size());
    Assert.assertEquals(0, Context.getGlobalContext().getConstantDecls().size());
    Assert.assertEquals(0, Context.getGlobalContext().getVariableDecls().size());
    Assert.assertEquals(0, Context.getGlobalContext().getModDefs().size());
    Assert.assertEquals(0, Context.getGlobalContext().getThmOrAssDefs().size());
  }

  @Test
  public void testOperatorInsertionOrderMaintained() {
    final ExternalModuleTable emt = new ExternalModuleTable();
    final Context ctx = Context.getGlobalContext().duplicate(emt);
    final List<OpDefNode> expected = new ArrayList<>();
    for (int i = 0; i < 100; i++) {
      final OpDefNode op = mkOpDef();
      expected.add(op);
      ctx.addSymbolToContext(op.getName(), op);
      Assert.assertTrue(ctx.occurSymbol(op.getName()));
      Assert.assertEquals(op, ctx.getSymbol(op.getName()));
    }

    for (final OpDefNode op : expected) {
      Assert.assertNotNull(ctx.getSymbol(op.getName()));
      Assert.assertTrue(ctx.occurSymbol(op.getName()));
    }

    ContextTest.assertContentsEqual(expected, ctx.content(), true);
    ContextTest.assertReversedIterableEqual(expected, ctx.getOpDefs());

    Assert.assertEquals(0, ctx.getConstantDecls().size());
    Assert.assertEquals(0, ctx.getVariableDecls().size());
    Assert.assertEquals(0, ctx.getModDefs().size());
    Assert.assertEquals(0, ctx.getThmOrAssDefs().size());
  }

  @Test
  public void testDuplicatePreservesInsertionOrder() {
    final ExternalModuleTable emt = new ExternalModuleTable();
    final Context ctx = Context.getGlobalContext().duplicate(emt);
    final List<OpDefNode> expected = new ArrayList<>();
    for (int i = 0; i < 100; i++) {
      final OpDefNode op = mkOpDef();
      expected.add(op);
      ctx.addSymbolToContext(op.getName(), op);
    }

    ContextTest.assertContentsEqual(expected, ctx.content(), true);
    ContextTest.assertReversedIterableEqual(expected, ctx.getOpDefs());
    final Context duplicate = ctx.duplicate(emt);
    ContextTest.assertContentsEqual(expected, duplicate.content(), true);
    ContextTest.assertReversedIterableEqual(expected, duplicate.getOpDefs());

    Assert.assertEquals(0, ctx.getConstantDecls().size());
    Assert.assertEquals(0, duplicate.getConstantDecls().size());
    Assert.assertEquals(0, ctx.getVariableDecls().size());
    Assert.assertEquals(0, duplicate.getVariableDecls().size());
    Assert.assertEquals(0, ctx.getModDefs().size());
    Assert.assertEquals(0, duplicate.getModDefs().size());
    Assert.assertEquals(0, ctx.getThmOrAssDefs().size());
    Assert.assertEquals(0, duplicate.getThmOrAssDefs().size());
  }

  @Test
  public void testMixedDefTypes() {
    final ExternalModuleTable emt = new ExternalModuleTable();
    final Context ctx = Context.getGlobalContext().duplicate(emt);
    final List<SymbolNode> all = new ArrayList<>();
    final List<OpDefNode> builtInOps = new ArrayList<>();
    for (final Context.Pair entry : ctx.content()) {
      builtInOps.add((OpDefNode)entry.getSymbol());
      all.add(entry.getSymbol());
    }
    final List<OpDefNode> ops = new ArrayList<>();
    final List<OpDefNode> instances = new ArrayList<>();
    final List<ModuleNode> modules = new ArrayList<>();
    final List<OpDeclNode> constants = new ArrayList<>();
    final List<OpDeclNode> variables = new ArrayList<>();
    final List<ThmOrAssumpDefNode> thmsAndAssumptions = new ArrayList<>();
    for (int i = 0; i < 100; i++) {
      final OpDefNode op = this.mkOpDef();
      ctx.addSymbolToContext(op.getName(), op);
      ops.add(op);
      all.add(op);
      final OpDefNode instance = this.mkInstance();
      ctx.addSymbolToContext(instance.getName(), instance);
      instances.add(instance);
      all.add(instance);
      final ModuleNode module = this.mkModule(ctx);
      ctx.addSymbolToContext(module.getName(), module);
      modules.add(module);
      all.add(module);
      final OpDeclNode constant = this.mkConstant();
      ctx.addSymbolToContext(constant.getName(), constant);
      constants.add(constant);
      all.add(constant);
      final OpDeclNode variable = this.mkVariable();
      ctx.addSymbolToContext(variable.getName(), variable);
      variables.add(variable);
      all.add(variable);
      final ThmOrAssumpDefNode theorem = this.mkTheorem();
      ctx.addSymbolToContext(theorem.getName(), theorem);
      thmsAndAssumptions.add(theorem);
      all.add(theorem);
      final ThmOrAssumpDefNode assumption = this.mkAssumption();
      ctx.addSymbolToContext(assumption.getName(), assumption);
      thmsAndAssumptions.add(assumption);
      all.add(assumption);
    }

    ContextTest.assertContentsEqual(all, ctx.content(), false);
    ContextTest.assertReversedIterableEqual(ops, ctx.getOpDefs());
    ContextTest.assertIterableEqual(modules, ctx.getModDefs());
    ContextTest.assertIterableEqual(constants, ctx.getConstantDecls());
    ContextTest.assertIterableEqual(variables, ctx.getVariableDecls());
    ContextTest.assertReversedIterableEqual(thmsAndAssumptions, ctx.getThmOrAssDefs());
  }

  @Test
  public void testMergeExtendContext() {
    final Errors log = new Errors();
    final ExternalModuleTable emt = new ExternalModuleTable();
    final Context base = Context.getGlobalContext().duplicate(emt);
    final Context extended = Context.getGlobalContext().duplicate(emt);
    final List<OpDefNode> ops = new ArrayList<>();
    for (int i = 0; i < 100; i++) {
      final OpDefNode op = this.mkOpDef();
      extended.addSymbolToContext(op.getName(), op);
      ops.add(op);
    }

    Assert.assertEquals(0, base.getOpDefs().size());
    ContextTest.assertReversedIterableEqual(ops, extended.getOpDefs());
    Assert.assertTrue(base.mergeExtendContext(extended, log));
    Assert.assertTrue(log.isSuccess());
    Assert.assertEquals(0, log.getWarningDetails().size());
    Assert.assertEquals(0, log.getErrorDetails().size());
    ContextTest.assertReversedIterableEqual(ops, extended.getOpDefs());
    ContextTest.assertReversedIterableEqual(ops, base.getOpDefs());
  }
}
