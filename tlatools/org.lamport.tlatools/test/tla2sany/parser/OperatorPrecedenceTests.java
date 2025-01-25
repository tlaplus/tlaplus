/*******************************************************************************
 * Copyright (c) 2024 Linux Foundation. All rights reserved.
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

import tla2sany.st.SyntaxTreeConstants;
import util.ParserAPI;

import org.junit.Assert;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.junit.Test;
import org.junit.Assume;

import java.util.ArrayList;
import java.util.List;

/**
 * Performs a large number of parse tests on prefix, infix, and postfix
 * operators focusing on their interaction through precedence and
 * associativity. This class generates on the order of 10,000 tests.
 */
@RunWith(Parameterized.class)
public class OperatorPrecedenceTests {

  /**
   * Whether an operator is a prefix, infix, or postfix operator.
   */
  public static enum FixKind {
    PREFIX,
    INFIX,
    POSTFIX
  }

  /**
   * Holds data describing the properties of an operator.
   */
  public static class Operator {

    /**
     * Whether the operator is prefix, infix, or postfix.
     */
    public final FixKind fix;

    /**
     * Operator symbol variants.
     */
    public final String[] symbols;

    /**
     * The lower bound of the operator precedence range.
     */
    public final int lowPrecedence;

    /**
     * The upper bound of the operator precedence range.
     */
    public final int highPrecedence;

    /**
     * Whether the operator is associative, in practice just left-
     * associative.
     */
    public final boolean associative;

    /**
     * Creates a new instance of the Operator class.
     *
     * @param fix The operator fix kind.
     * @param symbols The operator symbol alternatives.
     * @param low The operator precedence lower bound.
     * @param high The operator precedence upper bound.
     * @param associative Whether the operator is associative.
     */
    private Operator(FixKind fix, String[] symbols, int low, int high, boolean associative) {
      this.fix = fix;
      this.symbols = symbols;
      this.lowPrecedence = low;
      this.highPrecedence = high;
      this.associative = associative;
    }

    /**
     * True if this operator is lower precedence than the given one. This
     * means their ranges do not overlap at all and the range of this one
     * is entirely below the range of the other one.
     *
     * @param other The operator to compare against.
     * @return Whether this operator is lower precedence.
     */
    private boolean lowerPrecThan(Operator other) {
      return this.lowPrecedence < other.lowPrecedence
          && this.highPrecedence < other.highPrecedence;
    }

    /**
     * Whether this operator conflicts with the given other operator.
     * There are a number of cases to handle, documented in-line.
     *
     * @param other The operator to check against.
     * @return Whether this operator conflicts with the other operator.
     */
    private boolean conflictsWith(Operator other) {
      if (this.fix == other.fix && (FixKind.PREFIX == this.fix || FixKind.POSTFIX == this.fix)) {
        // Prefix & postfix ops can't really conflict with others in their class.
        return false;
      } else if (FixKind.INFIX == this.fix && FixKind.PREFIX == other.fix) {
        // Expressions such as A = ENABLED B are always unambiguous.
        return false;
      } else if (FixKind.POSTFIX == this.fix && FixKind.INFIX == other.fix) {
        // Expressions such as A' + B are always unambiguous.
        return false;
      } else if (this == other) {
        // Identical infix ops will conflict unless they are associative.
        return !this.associative;
      } else {
        // Conflicts if precedence range overlaps.
        return (this.lowPrecedence <= other.lowPrecedence && other.lowPrecedence <= this.highPrecedence) // overlap low
            || (this.lowPrecedence <= other.lowPrecedence && other.highPrecedence <= this.highPrecedence) // enclose
            || (other.lowPrecedence <= this.lowPrecedence && this.highPrecedence <= other.highPrecedence) // enclosed by
            || (this.lowPrecedence <= other.highPrecedence && other.highPrecedence <= this.highPrecedence); // overlap high
      }
    }

    /**
     * Used by JUnit to derive a unique name for the test case.
     *
     * @return A string identifying this class instance.
     */
    public String toString() {
      return this.symbols[0];
    }
  }

  /**
   * A basic syntactically valid module that can hold an expression.
   */
  public static final String PATTERN = "---- MODULE Test ----\nASSUME %s \n====";

  /**
   * All these operator precedence values are taken from the PDF "Summary
   * of TLA+" (https://lamport.azurewebsites.net/tla/summary-standalone.pdf)
   * with the exception of SUBSET, UNION, and DOMAIN which were incorrectly
   * documented as having precedences 8-8, 8-8, and 9-9 respectively; SANY
   * sets their precedences as 10-13. See this GitHub issue:
   * https://github.com/tlaplus/tlaplus/issues/892
   *
   * The very first string symbol in the array is the canonical symbol for
   * that operator.
   */
  public static final Operator[] OPERATORS = new Operator[] {
    new Operator(FixKind.PREFIX, new String[] {"\\lnot", "~", "\\neg"}, 4, 4, false),
    new Operator(FixKind.PREFIX, new String[] {"ENABLED"}, 4, 15, false),
    new Operator(FixKind.PREFIX, new String[] {"UNCHANGED"}, 4, 15, false),
    new Operator(FixKind.PREFIX, new String[] {"[]"}, 4, 15, false),
    new Operator(FixKind.PREFIX, new String[] {"<>"}, 4, 15, false),
    new Operator(FixKind.PREFIX, new String[] {"SUBSET"}, 10, 13, false),
    new Operator(FixKind.PREFIX, new String[] {"UNION"}, 10, 13, false),
    new Operator(FixKind.PREFIX, new String[] {"DOMAIN"}, 10, 13, false),
    new Operator(FixKind.PREFIX, new String[] {"-"}, 12, 12, false),
    new Operator(FixKind.INFIX, new String[] {"=>"}, 1, 1, false),
    new Operator(FixKind.INFIX, new String[] {"-+->"}, 2, 2, false),
    new Operator(FixKind.INFIX, new String[] {"\\equiv", "<=>"}, 2, 2, false),
    new Operator(FixKind.INFIX, new String[] {"~>"}, 2, 2, false),
    new Operator(FixKind.INFIX, new String[] {"\\lor", "\\/"}, 3, 3, true),
    new Operator(FixKind.INFIX, new String[] {"\\land", "/\\"}, 3, 3, true),
    new Operator(FixKind.INFIX, new String[] {"/=", "#"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"-|"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"::="}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {":="}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"<"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"="}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"=|"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {">"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\approx"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\asymp"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\cong"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\doteq"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\geq", ">="}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\gg"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\in"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\notin"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\leq", "<=", "=<"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\ll"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\prec"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\preceq"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\propto"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\sim"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\simeq"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\sqsubset"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\sqsubseteq"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\sqsupset"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\sqsupseteq"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\subset"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\subseteq"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\succ"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\succeq"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\supset"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\supseteq"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"|-"}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"|="}, 5, 5, false),
    new Operator(FixKind.INFIX, new String[] {"\\cdot"}, 5, 14, true),
    new Operator(FixKind.INFIX, new String[] {"@@"}, 6, 6, true),
    new Operator(FixKind.INFIX, new String[] {":>"}, 7, 7, false),
    new Operator(FixKind.INFIX, new String[] {"<:"}, 7, 7, false),
    new Operator(FixKind.INFIX, new String[] {"\\"}, 8, 8, false),
    new Operator(FixKind.INFIX, new String[] {"\\intersect", "\\cap"}, 8, 8, true),
    new Operator(FixKind.INFIX, new String[] {"\\union", "\\cup"}, 8, 8, true),
    new Operator(FixKind.INFIX, new String[] {".."}, 9, 9, false),
    new Operator(FixKind.INFIX, new String[] {"..."}, 9, 9, false),
    new Operator(FixKind.INFIX, new String[] {"!!"}, 9, 13, false),
    new Operator(FixKind.INFIX, new String[] {"##"}, 9, 13, true),
    new Operator(FixKind.INFIX, new String[] {"$"}, 9, 13, true),
    new Operator(FixKind.INFIX, new String[] {"$$"}, 9, 13, true),
    new Operator(FixKind.INFIX, new String[] {"??"}, 9, 13, true),
    new Operator(FixKind.INFIX, new String[] {"\\sqcap"}, 9, 13, true),
    new Operator(FixKind.INFIX, new String[] {"\\sqcup"}, 9, 13, true),
    new Operator(FixKind.INFIX, new String[] {"\\uplus"}, 9, 13, true),
    new Operator(FixKind.INFIX, new String[] {"\\wr"}, 9, 14, false),
    new Operator(FixKind.INFIX, new String[] {"\\oplus", "(+)"}, 10, 10, true),
    new Operator(FixKind.INFIX, new String[] {"+"}, 10, 10, true),
    new Operator(FixKind.INFIX, new String[] {"++"}, 10, 10, true),
    new Operator(FixKind.INFIX, new String[] {"%"}, 10, 11, false),
    new Operator(FixKind.INFIX, new String[] {"%%"}, 10, 11, true),
    new Operator(FixKind.INFIX, new String[] {"|"}, 10, 11, true),
    new Operator(FixKind.INFIX, new String[] {"||"}, 10, 11, true),
    new Operator(FixKind.INFIX, new String[] {"\\ominus", "(-)"}, 11, 11, true),
    new Operator(FixKind.INFIX, new String[] {"-"}, 11, 11, true),
    new Operator(FixKind.INFIX, new String[] {"--"}, 11, 11, true),
    new Operator(FixKind.INFIX, new String[] {"&"}, 13, 13, true),
    new Operator(FixKind.INFIX, new String[] {"&&"}, 13, 13, true),
    new Operator(FixKind.INFIX, new String[] {"\\odot", "(.)"}, 13, 13, true),
    new Operator(FixKind.INFIX, new String[] {"\\oslash", "(/)"}, 13, 13, false),
    new Operator(FixKind.INFIX, new String[] {"\\otimes", "(\\X)"}, 13, 13, true),
    new Operator(FixKind.INFIX, new String[] {"*"}, 13, 13, true),
    new Operator(FixKind.INFIX, new String[] {"**"}, 13, 13, true),
    new Operator(FixKind.INFIX, new String[] {"/"}, 13, 13, false),
    new Operator(FixKind.INFIX, new String[] {"//"}, 13, 13, false),
    new Operator(FixKind.INFIX, new String[] {"\\bigcirc"}, 13, 13, true),
    new Operator(FixKind.INFIX, new String[] {"\\bullet"}, 13, 13, true),
    new Operator(FixKind.INFIX, new String[] {"\\div"}, 13, 13, false),
    new Operator(FixKind.INFIX, new String[] {"\\o", "\\circ"}, 13, 13, true),
    new Operator(FixKind.INFIX, new String[] {"\\star"}, 13, 13, true),
    new Operator(FixKind.INFIX, new String[] {"^"}, 14, 14, false),
    new Operator(FixKind.INFIX, new String[] {"^^"}, 14, 14, false),
    new Operator(FixKind.POSTFIX, new String[] {"^+"}, 15, 15, false),
    new Operator(FixKind.POSTFIX, new String[] {"^*"}, 15, 15, false),
    new Operator(FixKind.POSTFIX, new String[] {"^#"}, 15, 15, false),
    new Operator(FixKind.POSTFIX, new String[] {"'"}, 15, 15, false),
  };

  /**
   * Given two operators, derive a syntactically-plausible expression that
   * uses them.
   *
   * @param op1 The operator which should appear first.
   * @param op1Symbol The symbol of the operator which should appear first.
   * @param op2 The operator which should appear second.
   * @param op2Symbol The symbol of the operator which should appear second.
   * @return A syntactically-plausible expression.
   */
  private static String deriveExpression(Operator op1, String op1Symbol, Operator op2, String op2Symbol) {
    switch (op1.fix) {
      case PREFIX: switch (op2.fix) {
        case PREFIX: return String.format("%s %s A", op1Symbol, op2Symbol);
        case INFIX: return String.format("%s A %s B", op1Symbol, op2Symbol);
        case POSTFIX: return String.format("%s A %s", op1Symbol, op2Symbol);
      }
      case INFIX: switch (op2.fix) {
        case PREFIX: return String.format("A %s %s B", op1Symbol, op2Symbol);
        case INFIX: return String.format("A %s B %s C", op1Symbol, op2Symbol);
        case POSTFIX: return String.format("A %s B %s", op1Symbol, op2Symbol);
      }
      case POSTFIX: switch (op2.fix) {
        case PREFIX: Assert.fail(); return "";
        case INFIX: return String.format("A %s %s B", op1Symbol, op2Symbol);
        case POSTFIX: return String.format("A %s %s", op1Symbol, op2Symbol);
      }
      default: Assert.fail(); return "";
    }
  }

  /**
   * Given a SANY parse tree of a module with a single ASSUME statement,
   * navigate to the expression node of that statement.
   *
   * @param root The root node of the parse tree.
   * @return The expression node of the ASSUME statement.
   */
  private static SyntaxTreeNode getExpressionInModule(SyntaxTreeNode root) {
    SyntaxTreeNode[] module = root.getHeirs();
    SyntaxTreeNode body = module[2];
    SyntaxTreeNode[] units = body.getHeirs();
    SyntaxTreeNode assume = units[0];
    return assume.getHeirs()[1];
  }

  /**
   * Given some sort of operator expression with a higher-precedence
   * operator as one of its children, find & return that child.
   *
   * @param lowerPrecOp The operator expression to look inside.
   * @return The higher-prec operator child of the given expression.
   */
  private static SyntaxTreeNode getHigherPrecOp(SyntaxTreeNode lowerPrecOp) {
    SyntaxTreeNode[] lowerPrecOpHeirs = lowerPrecOp.getHeirs();
    switch (lowerPrecOp.getKind()) {
      case SyntaxTreeConstants.N_PrefixExpr: return lowerPrecOpHeirs[1];
      case SyntaxTreeConstants.N_InfixExpr:
        return lowerPrecOpHeirs[0].isKind(SyntaxTreeConstants.N_GeneralId)
            ? lowerPrecOpHeirs[2]
            : lowerPrecOpHeirs[0];
      case SyntaxTreeConstants.N_PostfixExpr: return lowerPrecOpHeirs[0];
    }
    Assert.fail();
    return null;
  }

  /**
   * Given an operator expression, retrieves the string representation of
   * the operator being used.
   *
   * @param op The operator expression.
   * @return String representation of the operator being used.
   */
  private static String getOpImage(SyntaxTreeNode op) {
    SyntaxTreeNode[] opHeirs = op.getHeirs();
    switch (op.getKind()) {
      case SyntaxTreeConstants.N_PrefixExpr: return opHeirs[0].getHeirs()[1].getImage();
      case SyntaxTreeConstants.N_InfixExpr: return opHeirs[1].getHeirs()[1].getImage();
      case SyntaxTreeConstants.N_PostfixExpr: return opHeirs[1].getHeirs()[1].getImage();
    }
    Assert.fail();
    return null;
  }

  /**
   * Checks the parse tree to ensure the operators were parsed as expected.
   *
   * @param root The root of the parse tree.
   * @param op1 The operator appearing first.
   * @param op1Symbol The symbol of the operator appearing first.
   * @param op2 The operator appearing second.
   * @param op2Symbol The symbol of the operator appearing second.
   */
  private static void checkParsePrecedence(
      SyntaxTreeNode root,
      Operator op1,
      String op1Symbol,
      Operator op2,
      String op2Symbol
  ) {
    SyntaxTreeNode lowerPrecOp = getExpressionInModule(root);
    String lowerPrecOpSymbol = getOpImage(lowerPrecOp);
    SyntaxTreeNode higherPrecOp = getHigherPrecOp(lowerPrecOp);
    String higherPrecOpSymbol = getOpImage(higherPrecOp);
    if (op1 == op2) {
      if (op1.associative) {
        Assert.assertEquals(lowerPrecOpSymbol, op2Symbol);
        Assert.assertEquals(higherPrecOpSymbol, op1Symbol);
      } else {
        Assert.assertEquals(lowerPrecOpSymbol, op1Symbol);
        Assert.assertEquals(higherPrecOpSymbol, op2Symbol);
      }
    } else if (op1.lowerPrecThan(op2) || FixKind.PREFIX == op2.fix) {
      Assert.assertEquals(lowerPrecOpSymbol, op1Symbol);
      Assert.assertEquals(higherPrecOpSymbol, op2Symbol);
    } else {
      Assert.assertEquals(lowerPrecOpSymbol, op2Symbol);
      Assert.assertEquals(higherPrecOpSymbol, op1Symbol);
    }
  }

  /**
   * Generates all test cases.
   */
  @Parameters(name = "{index}: {1}, {3}")
  public static List<Object[]> getTests() {
    final List<Object[]> testCases = new ArrayList<Object[]>(14000);
    for (final Operator op1 : OPERATORS) {
      for (Operator op2 : OPERATORS) {
        if (FixKind.POSTFIX == op1.fix && FixKind.PREFIX == op2.fix) {
          // Can't construct a test case from this
          continue;
        }
        for (String op1Symbol : op1.symbols) {
          for (String op2Symbol : op2.symbols) {
            testCases.add(new Object[] { op1, op1Symbol, op2, op2Symbol });
          }
        }
      }
    }
    return testCases;
  }

  /**
   * The first operator to test; leftmost in the expression.
   */
  @Parameter(0)
  public Operator op1;

  /**
   * The specific symbol to use for the first operator.
   */
  @Parameter(1)
  public String op1Symbol;

  /**
   * The second operator to test; rightmost in the expression;
   */
  @Parameter(2)
  public Operator op2;

  /**
   * The specific symbol to use for the second operator.
   */
  @Parameter(3)
  public String op2Symbol;

  /**
   * Test whether the given operator combination is parsed correctly.
   */
  @Test
  public void testOperatorCombination() {
    // Skip this case because it's bugged; see
    // https://github.com/tlaplus/tlaplus/issues/893
    Assume.assumeFalse(
      FixKind.INFIX == op1.fix
      && FixKind.PREFIX == op2.fix
      && "-" == op2.symbols[0]
      && op2.lowerPrecThan(op1)
    );

    final String expr = deriveExpression(op1, op1Symbol, op2, op2Symbol);
    final String inputString = String.format(PATTERN, expr);
    final boolean expectParseSuccess = !op1.conflictsWith(op2);
    final SyntaxTreeNode parseTree = ParserAPI.processSyntax(inputString);
    final boolean actualParseSuccess = null != parseTree;
    Assert.assertEquals(expr, expectParseSuccess, actualParseSuccess);
    if (expectParseSuccess) {
      checkParsePrecedence(parseTree, this.op1, this.op1Symbol, this.op2, this.op2Symbol);
    }
  }
}
