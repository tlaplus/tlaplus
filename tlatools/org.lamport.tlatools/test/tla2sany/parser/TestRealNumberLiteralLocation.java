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
package tla2sany.parser;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import tla2sany.api.Frontend;
import tla2sany.api.ModuleSyntaxTree;
import tla2sany.api.Resolver;
import tla2sany.api.SANYFrontend;
import tla2sany.api.StringResolver;
import tla2sany.st.Location;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.st.TreeNode;

/**
 * Regression test for the reported location of real number literals without a
 * leading zero, e.g. {@code .5} (see GH tlaplus/tlaplus #596).
 *
 * <p>When a dot-led literal is parsed, {@link TLAplusParser#Number()} fabricates
 * a NUMBER_LITERAL token with image {@code "0"} for the empty integer part. That
 * artificial token must not shift the reported location of the N_Real node: it
 * carries the DOT's own location, so the node spans exactly the source of the
 * literal ({@code [dotColumn, lastDigitColumn]}), and tokens surrounding it keep
 * their tokenizer-derived positions.
 */
public class TestRealNumberLiteralLocation {

  private static final String MODULE = "---- MODULE Test ----\n"
      + "a == .5\n"
      + "b == 0.5\n"
      + "c == .5 + .25\n"
      + "d == .125\n"
      + "====\n";

  /**
   * Parses the module and returns the syntax tree root.
   */
  private static TreeNode parseModule() throws Exception {
    final Frontend parser = new SANYFrontend();
    final Resolver resolver = new StringResolver("Test", MODULE);
    final ModuleSyntaxTree syntaxTree = parser.processSyntax("Test", resolver);
    return syntaxTree.root;
  }

  /**
   * Collects all nodes of the given kind, in document order.
   */
  private static List<TreeNode> collect(final TreeNode node, final int kind) {
    final List<TreeNode> found = new ArrayList<>();
    collectInto(node, kind, found);
    return found;
  }

  private static void collectInto(final TreeNode node, final int kind, final List<TreeNode> found) {
    if (node.getKind() == kind) {
      found.add(node);
    }
    for (final TreeNode heir : node.heirs()) {
      collectInto(heir, kind, found);
    }
  }

  private static void assertLocation(
      final TreeNode node, final int beginLine, final int beginColumn, final int endLine,
      final int endColumn) {
    final Location loc = node.getLocation();
    Assert.assertEquals("beginLine", beginLine, loc.beginLine());
    Assert.assertEquals("beginColumn", beginColumn, loc.beginColumn());
    Assert.assertEquals("endLine", endLine, loc.endLine());
    Assert.assertEquals("endColumn", endColumn, loc.endColumn());
  }

  /**
   * The begin of a leading-zero-free real literal must be exactly where its DOT
   * token is (the first character of the literal), not one column to its left,
   * and the end must be the last fractional digit. The begin of {@code b} shows
   * the control case {@code 0.5} starts at its leading {@code 0}.
   */
  @Test
  public void testRealLiteralLocations() throws Exception {
    final TreeNode root = parseModule();
    final List<TreeNode> reals = collect(root, SyntaxTreeConstants.N_Real);
    Assert.assertEquals("expected four leading-zero-free literals plus one control", 5, reals.size());
    assertLocation(reals.get(0), 2, 6, 2, 7); // a == .5
    assertLocation(reals.get(1), 3, 6, 3, 8); // b == 0.5
    assertLocation(reals.get(2), 4, 6, 4, 7); // c == .5 + .25
    assertLocation(reals.get(3), 4, 11, 4, 13); // c == .5 + .25
    assertLocation(reals.get(4), 5, 6, 5, 9); // d == .125
  }

  /**
   * Locations of expressions surrounding a leading-zero-free literal must be
   * unaffected: the infix operator and the whole addition in {@code c} span
   * exactly from the first literal to the last.
   */
  @Test
  public void testSurroundingExpressionsNotShifted() throws Exception {
    final TreeNode root = parseModule();
    final List<TreeNode> infixes = collect(root, SyntaxTreeConstants.N_InfixExpr);
    Assert.assertEquals(1, infixes.size());
    assertLocation(infixes.get(0), 4, 6, 4, 13); // .5 + .25
  }
}