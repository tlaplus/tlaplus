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
package tla2sany.parser;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import tla2sany.output.SilentSanyOutput;
import static tla2sany.parser.TLAplusParserConstants.*;

/**
 * Tests for the critical but somewhat enigmatic {@link TLAplusParser#belchDEF()}
 * method. It *seems* to work by splicing {@link TLAplusParserConstants#DEFBREAK}
 * tokens into the token stream produced by {@link TLAplusParserTokenManager},
 * easing identification of the start of the next operator definition. However,
 * the method it uses to do this is very odd and involves modifying the pointer
 * {@link Token#next} in all the tokens in the series, then changing them back.
 * This has resulted in bugs like https://github.com/tlaplus/tlaplus/issues/430.
 */
@RunWith(Parameterized.class)
public class BelchDefTests {

  /**
   * A test case for {@link TLAplusParser#belchDEF()}.
   */
  public static class Case {

    /**
     * The human-readable name of the test.
     */
    public final String testName;

    /**
     * The number of tokens expected between each DEFBREAK token. This is
     * derived by splitting the given string on spaces then counting the
     * number of resulting substrings. Getting this right will require
     * providing test inputs in an idiomatic way, for example writing
     * op ( x ) == instead of op(x) ==.
     */
    public final List<Integer> expectedDefBreakPeriod = new ArrayList<>();

    /**
     * The parser instance to test.
     */
    public final TLAplusParser parser;

    public Case(String testName, String... inputs) {
      this.testName = testName;
      for (String input : inputs) {
        this.expectedDefBreakPeriod.add(input.split(" ").length);
      }

      this.parser = new TLAplusParser(
          new SilentSanyOutput(),
          TokenizerTests.wrapInModule(inputs).getBytes());
    }

    @Override
    public String toString() {
      return this.testName;
    }
  }

  /**
   * Generate all test cases for {@link TLAplusParser#belchDEF()}.
   *
   * @return A list of {@link TLAplusParser#belchDEF()} test cases.
   */
  @Parameters(name = "{index}: {0}")
  public static Case[] getCases() {
    return new Case[] {
        new Case("Empty module"),
        new Case("Single definition", "op == 0"),
        new Case("Multiple definitions", "op == 0", "op2 == 1"),
        new Case("Named theorem", "op == 0 THEOREM T == TRUE"),
        new Case("Named theorem after submodule", "op == 0 ---- MODULE Inner ---- ==== THEOREM T == TRUE"),
    };
  }

  /**
   * The current {@link TLAplusParser#belchDEF()} test case.
   */
  @Parameter
  public Case testCase;

  /**
   * Consumes the given number of tokens, calling {@link TLAplusParser#belchDEF()}
   * as appropriate.
   *
   * @param count The number of tokens to consume.
   */
  private void munch(int count) {
    for (int i = 0; i < count; i++) {
      // {@link TLAplusParser#belchDef()} is called right after consuming
      // the == token of the current operator definition.
      if (this.testCase.parser.getNextToken().kind == DEF) {
        this.testCase.parser.belchDEF();
      }
    }
  }

  /**
   * Runs a single DEFBREAK test case.
   */
  @Test
  public void runTestCase() {
    // Initialize parser tokens and consume module header.
    this.testCase.parser.belchDEF();
    Assert.assertEquals(EOF, this.testCase.parser.token.kind);
    Assert.assertNotEquals(EOF, this.testCase.parser.getNextToken().kind);
    munch(TokenizerTests.HEADER_TOKENS.size());

    // Iterate through groups of operator definition tokens separated by
    // DEFBREAK tokens. We consume period + 1 tokens to account for the extra
    // DEFBREAK token.
    for (int period : this.testCase.expectedDefBreakPeriod) {
      Assert.assertEquals(DEFBREAK, this.testCase.parser.token.kind);
      munch(period + 1);
    }

    // Consume module footer.
    munch(TokenizerTests.FOOTER_TOKENS.size());
  }
}
