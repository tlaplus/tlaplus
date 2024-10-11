package tla2sany.semantic;

import java.util.Arrays;
import java.util.Enumeration;

import org.junit.Assert;
import org.junit.Test;

import tla2sany.semantic.BuiltInOperators.BuiltInOperator;
import util.UniqueString;

/**
 * SANY statically initializes a table of built-in operators, like SUBSET,
 * UNION, DOMAIN, etc. These tests ensure that this initialization is done
 * correctly and completely.
 */
public class TestBuiltInOperatorInitialization {

  /**
   * Ensures all built-in operators are initialized as expected.
   */
  private void testCorrectAndComplete() {
    // Tests that all built-in operators are initialized as expected
    Context context = Context.getGlobalContext();
    for (BuiltInOperator expected : BuiltInOperators.Properties) {
      String name = expected.Name.toString();
      Assert.assertTrue(name, context.occurSymbol(expected.Name));
      SymbolNode node = context.getSymbol(expected.Name);
      Assert.assertTrue(name, node instanceof OpDefNode);
      OpDefNode actual = (OpDefNode)node;
      Assert.assertEquals(name, expected.Name, actual.getName());
      Assert.assertEquals(name, ASTConstants.BuiltInKind, actual.getKind());
      Assert.assertTrue(name, node.isBuiltIn());
      Assert.assertFalse(name, node.isStandardModule());
      Assert.assertFalse(name, node.isParam());
      Assert.assertFalse(name, actual.isLocal());
      Assert.assertNull(name, actual.getBody());
      Assert.assertEquals(name, expected.Arity, actual.getArity());
      if (expected.Arity == -1) {
        Assert.assertNull(name, actual.getParams());
      } else {
        Assert.assertEquals(name, expected.Arity, actual.getParams().length);
      }
      Assert.assertEquals(name, expected.OpLevel, actual.level);
      Assert.assertArrayEquals(name, expected.ArgMaxLevels, actual.getArgMaxLevels());
      Assert.assertArrayEquals(name, expected.ArgWeights, actual.getArgWeights());
    }

    // Ensure we are checking all built-in operators
    int builtInCount = 0;
    for (Enumeration<Context.Pair> e = Context.getGlobalContext().content(); e.hasMoreElements();) {
      UniqueString builtInName = e.nextElement().getSymbol().getName();
      Assert.assertTrue(builtInName.toString(), Arrays.stream(BuiltInOperators.Properties).anyMatch(op -> op.Name == builtInName));
      builtInCount++;
    }

    Assert.assertEquals(BuiltInOperators.Properties.length, builtInCount);
  }

  /**
   * Tests that initialization & re-initialization code sets the built-in
   * operator properties as expected.
   */
  @Test
  public void testInitAndReInit() {
    // First static initialization
    testCorrectAndComplete();

    // Re-initialization when parsing second file
    Context.reInit();
    testCorrectAndComplete();
  }
}