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
package tla2sany.drivers;

/**
 * The coarse-grained result of running SANY that is returned from its main
 * parsing functions like {@link SANY#parse} and also emitted as an exit
 * code when SANY is run from the command line. The exit code emitted from
 * those functions should correspond to {@link tla2sany.modanalyzer.SpecObj#getErrorLevel()},
 * but there likely exist code paths where this is not true. For programmatic
 * users, this exit code can be retrieved from {@link SANYExitException}.
 * Finer-grained {@link tla2sany.semantic.ErrorCode} instances can be found
 * in {@link tla2sany.modanalyzer.SpecObj#getParseErrors()} and
 * {@link tla2sany.modanalyzer.SpecObj#getSemanticErrors()}, which should
 * uniquely identify the actual error causing the parse failure in the cases
 * of {@link SanyExitCode#SYNTAX_PARSING_FAILURE} or
 * {@link SanyExitCode#SEMANTIC_ANALYSIS_OR_LEVEL_CHECKING_FAILURE}.
 */
public enum SanyExitCode {

  /**
   * Code returned when all is well, or when {@link SanySettings#doStrictErrorCodes}
   * is false.
   */
  OK (0),

  /**
   * Code returned when a failure occurs during the syntax parsing phase.
   */
  SYNTAX_PARSING_FAILURE (2),

  /**
   * Code returned when a failure occurs during the semantic analysis or
   * level-checking phases.
   */
  SEMANTIC_ANALYSIS_OR_LEVEL_CHECKING_FAILURE (4),

  /**
   * A very broad error code that encompasses everything from internal errors
   * to command-line argument parsing failures.
   */
  ERROR (-1);

  private final int code;

  private SanyExitCode(final int code) {
    this.code = code;
  }

  /**
   * The actual numerical error code to return on the command line.
   */
  public int code() {
    return this.code;
  }

  /**
   * Given a numerical code, derives this class's enumerated equivalent.
   * Throws {@link IllegalArgumentException} if the given code does not
   * correspond to a code in this enumeration.
   */
  public static SanyExitCode fromCode(final int code) {
    for (SanyExitCode exitCode : SanyExitCode.values()) {
      if (exitCode.code == code) {
        return exitCode;
      }
    }

    throw new IllegalArgumentException(Integer.toString(code));
  }
}
