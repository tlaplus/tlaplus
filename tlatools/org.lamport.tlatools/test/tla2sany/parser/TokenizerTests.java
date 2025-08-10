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

import java.io.ByteArrayInputStream;
import java.io.UnsupportedEncodingException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import static tla2sany.parser.TLAplusParserConstants.*;

/**
 * Tests for the parser's tokenizer, {@link TLAplusParserTokenManager}. This
 * is a stateful tokenizer, meaning that the interpretation of a given lexeme
 * changes depending on the tokenizer's state. The tokenizer state is stored
 * in {@link TLAplusParserTokenManager#curLexState}, and modified by calling
 * {@link TLAplusParserTokenManager#SwitchTo(int)} with an appropriate value.
 * The tokenizer itself also switches between states as appropriate based on
 * the tokens it consumes. For example, upon seeing a "---- MODULE" token
 * sequence, the tokenizer will stop treating text as pre-module comments and
 * start treating it as actual TLA+ tokens. There are currently six possible
 * tokenizer states:
 *
 *  - {@link TLAplusParserConstants#DEFAULT} is the initial tokenizer state.
 *    It treats all text as a free-form pre-module comment until finding the
 *    token sequence ---- MODULE, at which point it transitions to the
 *    {@link TLAplusParserConstants#SPEC} state.
 *
 *  - {@link TLAplusParserConstants#PRAGMA} is entered upon encountering a
 *    "--->" token in the pre-module text, and then tokenizes a list of
 *    numbers or identifiers. This seems unused and will likely be removed:
 *    https://github.com/tlaplus/tlaplus/issues/1227
 *
 *  - {@link TLAplusParserConstants#SPEC} is the core TLA+ tokenization state
 *    that is active when tokenizing a module.
 *
 *  - {@link TLAplusParserConstants#IN_COMMENT} is the state active when
 *    tokenizing TLA+ block comments.
 *
 *  - {@link TLAplusParserConstants#EMBEDDED} is the state entered into when
 *    tokenizing a nested TLA+ block comment.
 *
 *  - {@link TLAplusParserConstants#IN_EOL_COMMENT} is the state entered upon
 *    tokenizing TLA+ single-line comments.
 *
 * {@link TLAplusParserTokenManager#jjnewLexState} encodes state transitions;
 * the array is indexed with {@link TLAplusParserTokenManager#jjmatchedKind},
 * the value of which is calculated using indecipherable auto-generated bit
 * arithmetic. Almost all of the state transitions are -1, meaning undefined,
 * except for the following:
 *
 * | Index | State'         |
 * |-------|----------------|
 * | 2     | PRAGMA         |
 * | 3     | SPEC           |
 * | 21    | SPEC           |
 * | 27    | IN_COMMENT     |
 * | 28    | IN_EOL_COMMENT |
 * | 29    | EMBEDDED       |
 * | 30    | SPEC           |
 * | 33    | SPEC           |
 *
 * Since the transition table is auto-generated, these could change over time
 * arbitrarily. However, this snapshot is useful for gleaning understanding
 * of the state machine's structure, even if the indices are indecipherable.
 * We see that only one transition goes to PRAGMA, as expected since it can
 * only be found in one place - at the start of a file. Four transitions go
 * to SPEC, which makes sense - it can be transitioned to from the other four
 * states. One transition goes to IN_COMMENT, presumably from SPEC. One goes
 * to EMBEDDED, presumably when finding a nested comment while in IN_COMMENT.
 * One transition goes to IN_EOL_COMMENT, again presumably from SPEC. None of
 * the transitions naturally goes to the DEFAULT state; we can assume DEFAULT
 * transitions either to PRAGMA or SPEC depending on the start of the file.
 */
@RunWith(Parameterized.class)
public class TokenizerTests {

  /**
   * Basic module enclosure format, header & footer.
   */
  static final String MODULE_FORMAT = "---- MODULE Test ----\n%s\n====";

  /**
   * The expected tokenization of an ordinary module header.
   */
  static final List<Integer> HEADER_TOKENS = Arrays.asList(_BM1, IDENTIFIER, SEPARATOR);

  /**
   * The expected tokenization of an ordinary module footer.
   */
  static final List<Integer> FOOTER_TOKENS = Arrays.asList(END_MODULE, EOF);

  /**
   * Get all tokens found by the tokenizer.
   *
   * @param tokenizer The initialized tokenizer.
   * @return The tokens found by the provided tokenizer.
   */
  private static List<Integer> tokenize(TLAplusParserTokenManager tokenizer) {
    final List<Integer> tokens = new ArrayList<>();
    Token current = new Token();
    do {
      current = tokenizer.getNextToken();
      tokens.add(current.kind);
    } while (current.kind != EOF);

    return tokens;
  }

  /**
   * Wrap the given tokens in the standard module header & footer tokens.
   *
   * @param tokenKinds The token kinds to wrap in a header & footer.
   * @return A list of expected tokens.
   */
  static List<Integer> specTokens(Integer... tokenKinds) {
    final List<Integer> tokens = new ArrayList<>();
    tokens.addAll(HEADER_TOKENS);
    tokens.addAll(Arrays.asList(tokenKinds));
    tokens.addAll(FOOTER_TOKENS);
    return tokens;
  }

  /**
   * Wraps the given definitions within a module header & footer.
   *
   * @param definitions The definitions to wrap.
   * @return A fully-formed TLA+ module.
   */
  static String wrapInModule(final String... definitions) {
    final String units = String.join("\n", definitions);
    return String.format(MODULE_FORMAT, units);
  }

  /**
   * Convert the given list of string unit definitions into a
   * {@link SimpleCharStream} for consumption by the tokenizer,
   * encapsulated by a module header & footer.
   *
   * @param definitions The unit definitions to put in the module.
   * @return A stream ready for consumption by the tokenizer.
   */
  private static SimpleCharStream units(final String... definitions) {
    try {
      return new SimpleCharStream(
          new ByteArrayInputStream(wrapInModule(definitions).getBytes()),
          StandardCharsets.UTF_8.name(),
          1,
          1);
    } catch (UnsupportedEncodingException e) {
      Assert.fail(e.toString());
      return null;
    }
  }

  private static SimpleCharStream input(final String input) {
    try {
      final ByteArrayInputStream inputStream = new ByteArrayInputStream(input.getBytes());
      return new SimpleCharStream(inputStream, StandardCharsets.UTF_8.name(), 1, 1);
    } catch (UnsupportedEncodingException e) {
      Assert.fail(e.toString());
      return null;
    }
  }

  /**
   * A test case for the tokenizer.
   */
  public static class Case {

    /**
     * The human-readable test name.
     */
    public final String testName;

    /**
     * The state in which to initialize the tokenizer.
     */
    public final int startState;

    /**
     * The expected state in which the tokenizer ends up.
     */
    public final int expectedEndState;

    /**
     * The input to tokenize.
     */
    public final SimpleCharStream input;

    /**
     * The expected resulting list of tokens.
     */
    public final List<Integer> expectedTokenKinds;

    public Case(
        String testName,
        int startState,
        int expectedEndState,
        SimpleCharStream input,
        List<Integer> expectedTokenKinds
      ) {
      this.testName = testName;
      this.startState = startState;
      this.expectedEndState = expectedEndState;
      this.input = input;
      this.expectedTokenKinds = expectedTokenKinds;
    }

    @Override
    public String toString() {
      return this.testName;
    }
  }

  /**
   * Generate all test cases for the tokenizer.
   *
   * @return A list of tokenizer test cases.
   */
  @Parameters(name = "{index}: {0}")
  public static Case[] getCases() {
    return new Case[] {
        new Case("Empty module", DEFAULT,         SPEC,   units(), specTokens()),
        new Case("Constant",     DEFAULT,         SPEC,   units("CONSTANT x"), specTokens(CONSTANT, IDENTIFIER)),
        new Case("Constants",    DEFAULT,         SPEC,   units("CONSTANTS x, y"), specTokens(CONSTANT, IDENTIFIER, COMMA, IDENTIFIER)),
        new Case("Simple opdef", DEFAULT,         SPEC,   units("op == 0"), specTokens(IDENTIFIER, DEF, NUMBER_LITERAL)),
        new Case("Pragma mode",  DEFAULT,         PRAGMA, input("--->"), List.of(BEGIN_PRAGMA, EOF)),
        new Case("Pragma input", DEFAULT,         PRAGMA, input("---> id1 1 id2 2 id3 3"), List.of(BEGIN_PRAGMA, IDENTIFIER, NUMBER, IDENTIFIER, NUMBER, IDENTIFIER, NUMBER, EOF)),
        new Case("Pragma/spec",  DEFAULT,         SPEC,   input("---> 2 ---- MODULE"), List.of(BEGIN_PRAGMA, NUMBER, _BM2, EOF)),
        new Case("EOL comment",  IN_EOL_COMMENT,  SPEC,   input("\n"), List.of(EOF)),
        new Case("Block comment",IN_COMMENT,      SPEC,   input("*)"), List.of(EOF)),
    };
  }

  /**
   * The current tokenizer test case.
   */
  @Parameter
  public Case testCase;

  /**
   * Run the current tokenizer test case.
   */
  @Test
  public void runTokenizerCase() {
    final TLAplusParserTokenManager tokenizer = new TLAplusParserTokenManager(this.testCase.input);
    Assert.assertEquals(DEFAULT, tokenizer.curLexState);
    tokenizer.SwitchTo(this.testCase.startState);
    Assert.assertEquals(this.testCase.startState, tokenizer.curLexState);
    final List<Integer> actualTokens = tokenize(tokenizer);
    Assert.assertEquals(this.testCase.expectedEndState, tokenizer.curLexState);
    Assert.assertEquals(this.testCase.expectedTokenKinds, actualTokens);
  }
}
