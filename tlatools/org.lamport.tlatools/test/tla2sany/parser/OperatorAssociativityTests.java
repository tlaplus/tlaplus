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

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import util.ParserAPI;

import org.junit.Test;

/**
 * Exhaustive tests of operator associativity. Iterates through all standard
 * operators and tests whether expressions of the form "A + B + C" parse
 * correctly; if operators are marked as (left-)associative then parsing
 * should succeed, but if not it should fail.
 */
@RunWith(Parameterized.class)
public class OperatorAssociativityTests {

  /**
   * Generates all test cases.
   */
  @Parameters(name = "{index}: A {1} B {2} C")
  public static List<Object[]> getTests() {
    final List<Object[]> testCases = new ArrayList<Object[]>();
    for (final OperatorPrecedenceTests.Operator op : OperatorPrecedenceTests.OPERATORS) {
      if (OperatorPrecedenceTests.FixKind.INFIX != op.fix) {
        continue;
      }
      for (final String opSymbol1 : op.symbols) {
        for (final String opSymbol2 : op.symbols) {
          testCases.add(new Object[] { op, opSymbol1, opSymbol2 });
        }
      }
    }
    return testCases;
  }

  /**
   * The operator to test for associativity parsing correctness.
   */
  @Parameter(0)
  public OperatorPrecedenceTests.Operator op;

  /**
   * The specific symbol to use leftmost in the expression.
   */
  @Parameter(1)
  public String opSymbol1;

  /**
   * The specific symbol to use rightmost in the expression.
   */
  @Parameter(2)
  public String opSymbol2;

  /**
   * Test to ensure associative operators associate and non-associative
   * operators do not.
   */
  @Test
  public void testOperatorAssociativity() {
    final String expr = String.format("A %s B %s C", opSymbol1, opSymbol2);
    final String inputString = String.format(OperatorPrecedenceTests.PATTERN, expr);
    final boolean parseSuccess = null != ParserAPI.processSyntax(inputString);
    Assert.assertEquals(expr, op.associative, parseSuccess);
  }
}
