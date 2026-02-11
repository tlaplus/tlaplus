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
 * Encapsulates various settings controlling SANY execution. This is intended
 * to replace global static settings derived from parsing command line args
 * when SANY is run as a dependency of some other program.
 */
public final class SanySettings {

  /**
   * By default, SANY always returns 0 regardless of whether any stage of the
   * parsing process succeeded or failed. To maintain backwards compatibility
   * this setting was introduced, which if set to true makes SANY return a
   * nonzero error code on failure. External users of this class will always
   * have this setting set to true.
   */
  final boolean doStrictErrorCodes;

  /**
   * This setting controls whether, after parsing the raw TLA+ syntax, SANY
   * runs semantic analysis such as resolving identifier references. Usually
   * this is only desirable to disable if you are a developer trying to
   * analyze SANY behavior at the basic syntax parsing level.
   */
  public final boolean doSemanticAnalysis;

  /**
   * This setting controls whether, after running semantic analysis, SANY
   * performs level checking. If {@link SanySettings#doSemanticAnalysis} is
   * false, SANY will skip level checking regardless of this setting.
   */
  public final boolean doLevelChecking;

  /**
   * This setting controls whether, after running semantic analysis & level
   * checking, SANY runs linting. This will cause a failure if semantic
   * analysis was disabled.
   */
  public final boolean doLinting;

  /**
   * This setting controls whether to validate the PlusCal translation. This
   * means if the root spec contains a PlusCal block, SANY will run PlusCal
   * to check whether the PlusCal input or output have diverged from each
   * other and emit an appropriate warning if so. Neither the PlusCal nor its
   * translation will be modified.
   */
  public final boolean validatePCalTranslation;

  /**
   * Sensible default settings with meaningful error codes and all stages of
   * the validation process enabled. A good choice when you intend to present
   * SANY warnings & errors directly to the user.
   *
   * @return A {@link SanySettings} instance with sensible default settings.
   */
  public static SanySettings defaultSettings() {
    return new SanySettings(true, true, true, true);
  }

  /**
   * Settings to use when you only care about getting a valid Abstract Syntax
   * Tree from the TLA+ code; semantic analysis & level checking is performed
   * but linting and PlusCal validation is skipped. A good choice when your
   * tool intends to consume the AST for its own purposes and will otherwise
   * ignore warnings & linter messages.
   *
   * @return A {@link SanySettings} instance for only producing a valid AST.
   */
  public static SanySettings validAstSettings() {
    return new SanySettings(true, true, false, false);
  }

  /**
   * Use this constructor if you want full control over SANY settings.
   */
  public SanySettings(
      final boolean doSemanticAnalysis,
      final boolean doLevelChecking,
      final boolean doLinting,
      final boolean validatePCalTranslation) {
    this(
        true,
        doSemanticAnalysis,
        doLevelChecking,
        doLinting,
        validatePCalTranslation
      );
  }

  /**
   * For internal use only. Exposes the ability to disable strict error codes
   * for backwards compatibility, along with specifying the values of all
   * settings.
   */
  SanySettings(
      final boolean doStrictErrorCodes,
      final boolean doSemanticAnalysis,
      final boolean doLevelChecking,
      final boolean doLinting,
      final boolean validatePCalTranslation) {
    this.doStrictErrorCodes = doStrictErrorCodes;
    this.doSemanticAnalysis = doSemanticAnalysis;
    this.doLevelChecking = doLevelChecking;
    this.doLinting = doLinting;
    this.validatePCalTranslation = validatePCalTranslation;
  }
}
