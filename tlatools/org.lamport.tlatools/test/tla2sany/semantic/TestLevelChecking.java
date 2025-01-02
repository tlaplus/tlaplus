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

package tla2sany.semantic;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.junit.Assert;

import tla2sany.parser.SyntaxTreeNode;
import util.ParserAPI;

/**
 * Some basic tests for the level-checking process.
 */
@RunWith(Parameterized.class)
public class TestLevelChecking {

  /**
   * A test case for the level-checker.
   */
  private static class LevelCheckingTestCase {

    /**
     * Interpolate expressions into this string to form semantically-valid
     * TLA+ parse inputs.
     */
    private static final String INPUT_FORMAT_STRING =
      "---- MODULE Test ----\n" +
      "CONSTANT c\n" +
      "VARIABLE x\n" +
      "op == %s\n" +
      "====";

    /**
     * The expression to use for level checking.
     */
    public final String Expression;

    /**
     * The expected level-checking result on the input.
     */
    public final boolean ExpectedLevelCheckingResult;

    /**
     * Gets the expression interpolated in a parse-able module.
     * @return Valid TLA+ module source code.
     */
    public String getParseInput() {
      return String.format(INPUT_FORMAT_STRING, this.Expression);
    }

    /**
     * Initializes a new instance of the {@link LevelCheckingTestCase} class.
     *
     * @param expression An expression to interpolate into a module body.
     * @param expected The expected level-checking result on the input.
     */
    public LevelCheckingTestCase(String expression, boolean expected) {
      this.Expression = expression;
      this.ExpectedLevelCheckingResult = expected;
    }

    /**
     * Summarize this test for error reporting purposes.
     *
     * @param log The semantic & level-checker error log.
     * @return A string summary of the test and its result.
     */
    public String summarize(Errors log) {
      return String.format(
        "Input:\n%s\nLog:\n%s",
        this.getParseInput(), log.toString());
    }

    /**
     * Used by JUnit as the name of the parameterized test.
     * @return The name to give this test instance.
     */
    public String toString() {
      return this.Expression;
    }
  }

  /**
   * A corpus of tests for the level-checker.
   */
  @Parameters(name = "{index}: {0}")
  public static LevelCheckingTestCase[] testCases() {
    return new LevelCheckingTestCase[] {
      /**
       * Before some refactoring to remove the config.jj parser that
       * initialized the various built-in operators and their levels, the \lnot
       * operator (logical negation) also had its synonym \neg initialized as a
       * built-in operator. Theoretically this should not be necessary, since
       * operator synonym resolution should happen before any operator details
       * are fetched. Here we test whether that hypothesis is true.
       */
      new LevelCheckingTestCase("\\neg c",         true),

      /**
       * Also during the work to remove config.jj, it was found that the dot .
       * record access operator did not have its level constraints set. This
       *   was eventually found to not be an issue because it had its constraints
       * set as $RcdSelect instead the "." representation. Here we test that
       * this hypothesis is true. For further info, see this issue:
       * https://github.com/tlaplus/tlaplus/issues/1008
       */
      new LevelCheckingTestCase("c.foo",           true),

      /**
       * This is another test of the dot record access operator to ensure it is
       * actually possible to go beyond its level constraints, so they are set
       * appropriately.
       */
      new LevelCheckingTestCase("([]c).foo",       false),

      /**
       * Various tests to increase coverage of {@link OpApplNode} level-
       * checking, especially with regard to temporal operators and their
       * unicode equivalents.
       */
      // Constant-level parameters
      new LevelCheckingTestCase("[]c",             true),
      new LevelCheckingTestCase("□c",              true),
      new LevelCheckingTestCase("<>c",             true),
      new LevelCheckingTestCase("◇c",              true),

      // Variable-level parameters
      new LevelCheckingTestCase("[]x",             true),
      new LevelCheckingTestCase("□x",              true),
      new LevelCheckingTestCase("<>x",             true),
      new LevelCheckingTestCase("◇x",              true),

      // Action-level parameters
      new LevelCheckingTestCase("[](x')",          false),
      new LevelCheckingTestCase("□(x')",           false),
      new LevelCheckingTestCase("<>(x')",          false),
      new LevelCheckingTestCase("◇(x')",           false),
      new LevelCheckingTestCase("[][c]_x",         true),
      new LevelCheckingTestCase("□[c]_x",          true),
      new LevelCheckingTestCase("[]<<c>>_x",       false),
      new LevelCheckingTestCase("□⟨c⟩_x",          false),
      new LevelCheckingTestCase("<><<c>>_x",       true),
      new LevelCheckingTestCase("◇⟨c⟩_x",          true),
      new LevelCheckingTestCase("<>[c]_x",         false),
      new LevelCheckingTestCase("◇[c]_x",          false),

      // Leads-to and plus-arrow
      new LevelCheckingTestCase("c ~> c",          true),
      new LevelCheckingTestCase("x' ~> c",         false),
      new LevelCheckingTestCase("c ~> x'",         false),
      new LevelCheckingTestCase("c ↝ c",           true),
      new LevelCheckingTestCase("x' ↝ c",          false),
      new LevelCheckingTestCase("c ↝ x'",          false),
      new LevelCheckingTestCase("c -+-> c",        true),
      new LevelCheckingTestCase("x' -+-> c",       false),
      new LevelCheckingTestCase("c -+-> x'",       false),
      new LevelCheckingTestCase("c ⇸ c",           true),
      new LevelCheckingTestCase("x' ⇸ c",          false),
      new LevelCheckingTestCase("c ⇸ x'",          false),

      // Infix ops can have temporal or action but not both
      new LevelCheckingTestCase("c /\\ c",         true),
      new LevelCheckingTestCase("c ∧ c",           true),
      new LevelCheckingTestCase("x /\\ c",         true),
      new LevelCheckingTestCase("x ∧ c",           true),
      new LevelCheckingTestCase("[]c /\\ c",       true),
      new LevelCheckingTestCase("□c ∧ c",          true),
      new LevelCheckingTestCase("c /\\ x'",        true),
      new LevelCheckingTestCase("c ∧ x'",          true),
      new LevelCheckingTestCase("[]c /\\ x'",      false),
      new LevelCheckingTestCase("□c ∧ x'",         false),

      // Quantifiers & temporal formulas
      new LevelCheckingTestCase("∀ v ∈ c  : v",    true),
      new LevelCheckingTestCase("∃ v ∈ x  : v",    true),
      new LevelCheckingTestCase("∀ v ∈ x' : v",    true),
      new LevelCheckingTestCase("∃ v ∈ x  : □v",   true),
      new LevelCheckingTestCase("∀ v ∈ x' : □v",   false),
      new LevelCheckingTestCase("∃ v ∈ □x : v",    false),
    };
  }

  @Parameter
  public LevelCheckingTestCase testCase;

  /**
   * Runs all level-checker tests in the corpus.
   */
  @Test
  public void testAll() {
    SyntaxTreeNode parseTree = ParserAPI.processSyntax(testCase.getParseInput());
    Errors semanticLog = new Errors();
    ModuleNode semanticTree = ParserAPI.processSemantics(parseTree, semanticLog);
    Assert.assertTrue(testCase.summarize(semanticLog), semanticLog.isSuccess());
    Errors levelCheckingLog = new Errors();
    boolean actualLevelCheckingResult = ParserAPI.checkLevel(semanticTree, levelCheckingLog);
    Assert.assertTrue(testCase.summarize(semanticLog), semanticLog.isSuccess());
    Assert.assertEquals(testCase.summarize(levelCheckingLog), levelCheckingLog.isSuccess(), actualLevelCheckingResult);
    Assert.assertEquals(testCase.summarize(levelCheckingLog), testCase.ExpectedLevelCheckingResult, actualLevelCheckingResult);
  }
}