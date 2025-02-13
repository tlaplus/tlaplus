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

import java.util.Arrays;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * An enumeration of standardized codes for errors during semantic checking.
 */
public enum ErrorCode {

  UNSPECIFIED (0, ErrorLevel.UNDEFINED),
  EXTENDED_MODULES_SYMBOL_UNIFICATION_AMBIGUITY (1000, ErrorLevel.WARNING),
  EXTENDED_MODULES_SYMBOL_UNIFICATION_CONFLICT (2000, ErrorLevel.ERROR);

  public static enum ErrorLevel {
    UNDEFINED,
    WARNING,
    ERROR,
    ABORT
  }

  public final int value;

  public final ErrorLevel level;

  private ErrorCode(int value, ErrorLevel level) {
    this.value = value;
    this.level = level;
  }

  /**
   * A static map from error code value to enum to avoid linear lookups.
   */
  private static final Map<Integer, ErrorCode> codeMap =
    Arrays
      .stream(ErrorCode.values())
      .collect(Collectors.toMap(code -> code.value, code -> code));

  public static ErrorCode fromStandardValue(final int value) {
    final ErrorCode code = ErrorCode.codeMap.get(value);
    if (null == code) {
      throw new IllegalArgumentException(Integer.toString(value));
    }
    return code;
  }
}
