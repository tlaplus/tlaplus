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
 * Recorded in the {@link Errors} class. Since the error codes are standard
 * they will not be documented here; they should be explained in external
 * documentation. Some preliminary error codes are not standardized so have
 * been documented with comments.
 */
public enum ErrorCode {

  /**
   * Used if no error code is provided when logging an error. Ideally every
   * error logged should have an associated error code.
   */
  UNSPECIFIED (0, ErrorLevel.UNDEFINED),

  /**
   * Used for internal errors that function more like assertions; should
   * likely be replaced with thrown runtime exceptions. These errors are more
   * artifacts of the specific method SANY uses for validation than general
   * cases that should be standardized.
   */
  INTERNAL_ERROR (1, ErrorLevel.UNDEFINED),

  /**
   * Many error checks are duplicates of earlier error checks, so the process
   * terminates before ever reaching that point. To some degree this means
   * the checks function more as internal errors, assertions about the state
   * at that point in the program. This assists in programmer comprehension
   * as the semantic checking code is very large and it is difficult to know
   * what has or has not yet been checked at any given point. However, it is
   * useful to tag these error checks with this error code as possible basis
   * for future action. Note that it also says *suspected* - it is certainly
   * possible that some parse input could evade all prior error checks and
   * make it to the error check in question, it just hasn't yet been found.
   * If a user manages to trigger an error with this error code, that counts
   * as a bug in the parser that should be reified with an actual error code.
   *
   * Arity checks are a very common class of errors tagged with this code:
   * the match between the arity of an operator and an application of it is
   * checked many times in the codebase, and almost all of these checks will
   * never be reached since the semantic checking process will have failed
   * before those points.
   */
  SUSPECTED_UNREACHABLE_CHECK (2, ErrorLevel.UNDEFINED),

  /**
   * SANY contains some code handling language features that are either not
   * part of the known language standard, being considered for removal from
   * the language standard, or overwhelmingly likely to eventually be removed
   * from the language standard; error-checking code for these features is
   * tagged with this code since it is not worth expending development effort
   * on standardizing those errors and creating tests for them. If the feature
   * manages to - against all odds - escape purgatory and become more widely
   * supported and used, code tagged with this error can be promoted to using
   * standardized errors with associated tests.
   *
   * Subexpressions are one prominent category of language feature tagged
   * with this error code.
   */
  UNSUPPORTED_LANGUAGE_FEATURE (3, ErrorLevel.UNDEFINED),

  /**
   * Standardized warnings. These should not cause a parse failure.
   */
  EXTENDED_MODULES_SYMBOL_UNIFICATION_AMBIGUITY (1000, ErrorLevel.WARNING),
  INSTANCED_MODULES_SYMBOL_UNIFICATION_AMBIGUITY (1001, ErrorLevel.WARNING),

  /**
   * Standardized errors. These should cause a parse failure.
   */
  EXTENDED_MODULES_SYMBOL_UNIFICATION_CONFLICT (2000, ErrorLevel.ERROR),
  ALWAYS_PROPERTY_SENSITIVE_TO_STUTTERING (2001, ErrorLevel.ERROR),
  EVENTUALLY_PROPERTY_SENSITIVE_TO_STUTTERING (2002, ErrorLevel.ERROR),
  BINARY_TEMPORAL_OPERATOR_WITH_ACTION_LEVEL_PARAMETER (2003, ErrorLevel.ERROR),
  LOGICAL_OPERATOR_WITH_MIXED_ACTION_TEMPORAL_PARAMETERS (2004, ErrorLevel.ERROR),
  QUANTIFIED_TEMPORAL_FORMULA_WITH_ACTION_LEVEL_BOUND (2005, ErrorLevel.ERROR),
  SYMBOL_REDEFINED (2006, ErrorLevel.ERROR),
  BUILT_IN_SYMBOL_REDEFINED (2007, ErrorLevel.ERROR),
  MODULE_REDEFINED (2008, ErrorLevel.ERROR),
  INSTANCE_SUBSTITUTION_SYMBOL_REDEFINED_MULTIPLE_TIMES (2009, ErrorLevel.ERROR),
  INSTANCE_SUBSTITUTION_ILLEGAL_SYMBOL_REDEFINITION (2010, ErrorLevel.ERROR),
  ASSUMPTION_IS_NOT_CONSTANT (2011, ErrorLevel.ERROR),
  USE_OR_HIDE_FACT_NOT_VALID (2012, ErrorLevel.ERROR),
  TEMPORAL_PROOF_GOAL_WITH_NON_CONSTANT_TAKE_WITNESS_HAVE (2013, ErrorLevel.ERROR),
  TEMPORAL_PROOF_GOAL_WITH_NON_CONSTANT_CASE (2014, ErrorLevel.ERROR),
  QUANTIFIED_TEMPORAL_PICK_FORMULA_WITH_NON_CONSTANT_BOUND (2015, ErrorLevel.ERROR),
  OPERATOR_NAME_INCOMPLETE (2016, ErrorLevel.ERROR),
  INSTANCE_SUBSTITUTION_MISSING_SYMBOL (2017, ErrorLevel.ERROR),
  OPERATOR_LEVEL_CONSTRAINTS_EXCEEDED (2018, ErrorLevel.ERROR),
  QUANTIFICATION_WITH_TEMPORAL_LEVEL_BOUND (2019, ErrorLevel.ERROR),
  HIGHER_ORDER_OPERATOR_PARAMETER_LEVEL_CONSTRAINT_NOT_MET (2020, ErrorLevel.ERROR),
  HIGHER_ORDER_OPERATOR_COPARAMETER_LEVEL_CONSTRAINTS_EXCEEDED (2021, ErrorLevel.ERROR),
  OPERATOR_GIVEN_INCORRECT_NUMBER_OF_ARGUMENTS (2022, ErrorLevel.ERROR),
  HIGHER_ORDER_OPERATOR_ARGUMENT_HAS_INCORRECT_ARITY (2023, ErrorLevel.ERROR),
  HIGHER_ORDER_OPERATOR_REQUIRED_BUT_EXPRESSION_GIVEN (2024, ErrorLevel.ERROR),
  LAMBDA_OPERATOR_ARGUMENT_HAS_INCORRECT_ARITY (2025, ErrorLevel.ERROR),
  LAMBDA_GIVEN_WHERE_EXPRESSION_REQUIRED (2026, ErrorLevel.ERROR),
  ASSUME_PROVE_NEW_CONSTANT_HAS_TEMPORAL_LEVEL_BOUND (2027, ErrorLevel.ERROR),
  RECURSIVE_OPERATOR_PRIMES_PARAMETER (2028, ErrorLevel.ERROR),
  INSTANCE_SUBSTITUTION_LEVEL_CONSTRAINTS_EXCEEDED (2029, ErrorLevel.ERROR),
  INSTANCE_SUBSTITUTION_OPERATOR_CONSTANT_INCORRECT_ARITY (2030, ErrorLevel.ERROR),
  RECURSIVE_OPERATOR_DECLARED_BUT_NOT_DEFINED (2031, ErrorLevel.ERROR),
  RECURSIVE_SECTION_CONTAINS_ILLEGAL_DEFINITION (2032, ErrorLevel.ERROR),
  LABEL_PARAMETER_REPETITION (2033, ErrorLevel.ERROR),
  LABEL_PARAMETER_MISSING (2034, ErrorLevel.ERROR),
  LABEL_PARAMETER_UNNECESSARY (2035, ErrorLevel.ERROR),
  FUNCTION_EXCEPT_AT_USED_WHERE_UNDEFINED (2036, ErrorLevel.ERROR),
  FUNCTION_GIVEN_INCORRECT_NUMBER_OF_ARGUMENTS (2037, ErrorLevel.ERROR),
  LABEL_NOT_IN_DEFINITION_OR_PROOF_STEP (2038, ErrorLevel.ERROR),
  LABEL_NOT_ALLOWED_IN_NESTED_ASSUME_PROVE_WITH_NEW (2039, ErrorLevel.ERROR),
  LABEL_NOT_ALLOWED_IN_FUNCTION_EXCEPT (2040, ErrorLevel.ERROR),
  LABEL_REDEFINITION (2041, ErrorLevel.ERROR),
  PROOF_STEP_WITH_IMPLICIT_LEVEL_CANNOT_HAVE_NAME (2042, ErrorLevel.ERROR),
  SYMBOL_UNDEFINED (2043, ErrorLevel.ERROR),
  RECURSIVE_OPERATOR_DECLARATION_DEFINITION_ARITY_MISMATCH (2044, ErrorLevel.ERROR),
  RECURSIVE_OPERATOR_DEFINED_IN_WRONG_LET_IN_LEVEL (2045, ErrorLevel.ERROR),
  RECORD_CONSTRUCTOR_FIELD_REDEFINITION (2046, ErrorLevel.ERROR),
  LABEL_GIVEN_INCORRECT_NUMBER_OF_ARGUMENTS (2047, ErrorLevel.ERROR),
  MODULE_FILE_CANNOT_BE_FOUND (2048, ErrorLevel.ERROR),
  MODULE_DEPENDENCIES_ARE_CIRCULAR (2049, ErrorLevel.ERROR),
  MODULE_NAME_DIFFERENT_FROM_FILE_NAME (2050, ErrorLevel.ERROR);

  public static enum ErrorLevel {
    UNDEFINED,
    WARNING,
    ERROR
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
