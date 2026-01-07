/*******************************************************************************
 * Copyright (c) 2025 Linux Foundation. All rights reserved.
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

import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import org.junit.Assert;
import org.junit.Test;

import tla2sany.output.SilentSanyOutput;
import tla2sany.parser.IncrementalSyntaxParseTests;
import tla2sany.parser.ParseException;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.parser.TLAplusParser;
import util.TLAConstants;
import util.ToolIO;
import util.UniqueString;

/**
 * Tests exploring the possibility of parsing individual operator definitions
 * or expressions instead of requiring full module encapsulation. Related to
 * {@link IncrementalSyntaxParseTests}, but also checks semantics and levels.
 */
public class IncrementalSemanticParseTests {

  /**
   * Populates an {@link ExternalModuleTable} with imported standard modules.
   *
   * @param dependencies Module names to resolve.
   * @return A table of resolved modules.
   * @throws AbortException If semantic checking of the modules fails.
   */
  private static ExternalModuleTable resolveDependencies(String... dependencies) throws AbortException {
    return resolveDependencies(new ExternalModuleTable(), dependencies);
  }

  private static ExternalModuleTable resolveDependencies(ExternalModuleTable emt, String... dependencies) throws AbortException {
    for (String moduleName : dependencies) {
      try (final InputStream moduleSource = new FileInputStream(
				ToolIO.getDefaultResolver().resolve(moduleName + TLAConstants.Files.TLA_EXTENSION, false))) {

    	final TLAplusParser parser = new TLAplusParser(new SilentSanyOutput(), moduleSource);
        Assert.assertTrue(parser.parse());
        
        // Transitively resolve dependencies.
		for (String dep : parser.dependencies()) {
			if (emt.getModuleNode(dep) == null) {
				resolveDependencies(emt, dep);
			}
		}
        
        final Errors log = new Errors();
        final Generator semanticParser = new Generator(emt, log);
        final ModuleNode module = semanticParser.generate(parser.rootNode());
        Assert.assertTrue(log.toString(), log.isSuccess());
        module.levelCheck(log);
        Assert.assertTrue(log.toString(), log.isSuccess());
        emt.put(UniqueString.of(moduleName), semanticParser.getSymbolTable().getExternalContext(), module);
      } catch (IOException e) {
        throw new RuntimeException("ERROR: Unable to read module " + moduleName);
      }
    }
    return emt;
  }

  @Test
  public void basicOpDefTest() throws ParseException, AbortException {
    final SyntaxTreeNode syntax = IncrementalSyntaxParseTests.parser("op == 0").OperatorOrFunctionDefinition();
    final Errors log = new Errors();
    final Generator semantic = new Generator(null, log);
    final OpDefNode result = semantic.processOperator(syntax, null, null);
    Assert.assertTrue(log.toString(), log.isSuccess());
    Assert.assertNotNull(result);
    Assert.assertEquals("op", result.getName().toString());
    Assert.assertEquals(0, result.getArity());
    Assert.assertFalse(result.getInRecursive());
    result.levelCheck(log);
    Assert.assertTrue(log.toString(), log.isSuccess());
    Assert.assertEquals(syntax, result.getTreeNode());
    Assert.assertEquals(LevelConstants.ConstantLevel, result.getLevel());
    Assert.assertEquals(NumeralNode.class, result.getBody().getClass());
  }

  @Test
  public void basicExpressionTest() throws ParseException, AbortException {
    final SyntaxTreeNode syntax = IncrementalSyntaxParseTests.parser("0").Expression();
    final Errors log = new Errors();
    final Generator semantic = new Generator(null, log);
    final ExprNode result = semantic.generateExpression(syntax, new ModuleNode(null, null, null));
    Assert.assertTrue(log.toString(), log.isSuccess());
    Assert.assertNotNull(result);
    result.levelCheck(log);
    Assert.assertTrue(log.toString(), log.isSuccess());
    Assert.assertEquals(syntax, result.getTreeNode());
    Assert.assertEquals(LevelConstants.ConstantLevel, result.getLevel());
    Assert.assertEquals(NumeralNode.class, result.getClass());
  }

  @Test
  public void letInExpressionTest() throws ParseException, AbortException {
    final TLAplusParser parser = IncrementalSyntaxParseTests.parser("LET M == INSTANCE Naturals IN M!+(1, 2)");
    final SyntaxTreeNode syntax = parser.Expression();
    Assert.assertEquals(1, parser.dependencies().length);
    Assert.assertEquals("Naturals", parser.dependencies()[0]);
    final ExternalModuleTable emt = resolveDependencies(parser.dependencies());
    Assert.assertNotNull(emt.getModuleNode("Naturals"));
    final Errors log = new Errors();
    final Generator semantic = new Generator(emt, log);
    final ExprNode result = semantic.generateExpression(syntax, new ModuleNode(null, null, null));
    Assert.assertTrue(log.toString(), log.isSuccess());
    Assert.assertNotNull(result);
    result.levelCheck(log);
    Assert.assertTrue(log.toString(), log.isSuccess());
    Assert.assertEquals(syntax, result.getTreeNode());
    Assert.assertEquals(LevelConstants.ConstantLevel, result.getLevel());
    Assert.assertEquals(LetInNode.class, result.getClass());
    final LetInNode actual = (LetInNode)result;
    Assert.assertEquals(OpApplNode.class, actual.getBody().getClass());
    final OpApplNode actualOp = (OpApplNode)actual.getBody();
    Assert.assertEquals(OpDefNode.class, actualOp.getOperator().getClass());
    final OpDefNode actualOpRef = (OpDefNode)actualOp.getOperator();
    Assert.assertEquals(emt.getModuleNode("Naturals").getOpDef("+"), actualOpRef.getSource());
  }

  @Test
  public void letInExpressionWithTransitiveDepsTest() throws ParseException, AbortException {
    final TLAplusParser parser = IncrementalSyntaxParseTests.parser("LET T == INSTANCE TLC IN T!JavaTime");
    final SyntaxTreeNode syntax = parser.Expression();
    Assert.assertEquals(1, parser.dependencies().length);
    Assert.assertEquals("TLC", parser.dependencies()[0]);
    final ExternalModuleTable emt = resolveDependencies(parser.dependencies());
    Assert.assertNotNull(emt.getModuleNode("Naturals"));
    Assert.assertNotNull(emt.getModuleNode("Sequences"));
    Assert.assertNotNull(emt.getModuleNode("FiniteSets"));
    final Errors log = new Errors();
    final Generator semantic = new Generator(emt, log);
    final ExprNode result = semantic.generateExpression(syntax, new ModuleNode(null, null, null));
    Assert.assertTrue(log.toString(), log.isSuccess());
    Assert.assertNotNull(result);
    result.levelCheck(log);
    Assert.assertTrue(log.toString(), log.isSuccess());
    Assert.assertEquals(syntax, result.getTreeNode());
    Assert.assertEquals(LevelConstants.ConstantLevel, result.getLevel());
    Assert.assertEquals(LetInNode.class, result.getClass());
    final LetInNode actual = (LetInNode)result;
    Assert.assertEquals(OpApplNode.class, actual.getBody().getClass());
    final OpApplNode actualOp = (OpApplNode)actual.getBody();
    Assert.assertEquals(OpDefNode.class, actualOp.getOperator().getClass());
    final OpDefNode actualOpRef = (OpDefNode)actualOp.getOperator();
    Assert.assertEquals(emt.getModuleNode("TLC").getOpDef("JavaTime"), actualOpRef.getSource());
  }
}
