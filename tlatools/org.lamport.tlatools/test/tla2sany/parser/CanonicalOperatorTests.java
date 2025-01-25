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
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import util.UniqueString;

/**
* SANY has the concept of a "canonical" operator representation, since some
* operators have multiple possible symbols associated with them. This tests
* that the canonical operator is as expected.
*/
@RunWith(Parameterized.class)
public class CanonicalOperatorTests {

  /**
   * Generates all test cases.
   */
  @Parameters(name = "{index}: {0}")
  public static List<OperatorPrecedenceTests.Operator> getTests() {
    final List<OperatorPrecedenceTests.Operator> testCases = new ArrayList<>();
    for (final OperatorPrecedenceTests.Operator op : OperatorPrecedenceTests.OPERATORS) {
      testCases.add(op);
    }
    return testCases;
  }

  /**
   * The operator to test for canonical correctness.
   */
  @Parameter
  public OperatorPrecedenceTests.Operator op;

  /**
   * Tests that the {@link Operators} class resolves all operator synonyms
   * to their correct canonical form.
   */
  @Test
  public void testCanonicalOperatorCorrectness() {
    String expected = op.symbols[0];
    for (String symbol : op.symbols) {
      UniqueString symbolUnique = UniqueString.uniqueStringOf(symbol);
      Assert.assertTrue(Operators.existsOperator(symbolUnique));
      Assert.assertEquals(expected, Operators.resolveSynonym(symbolUnique).toString());
    }
  }
}
