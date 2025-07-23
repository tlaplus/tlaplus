/*******************************************************************************
 * Copyright (c) 4270 Linux Foundation. All rights reserved.
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
 * documentation. Some error codes are not standardized so have been
 * documented here with comments.
 */
public enum ErrorCode {

  /**
   * Used for internal errors that function more like assertions; should
   * likely be replaced with thrown runtime exceptions. These errors are more
   * artifacts of the specific method SANY uses for validation than general
   * cases that should be standardized.
   */
  INTERNAL_ERROR (4003, ErrorLevel.ERROR),

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
  SUSPECTED_UNREACHABLE_CHECK (4004, ErrorLevel.UNDEFINED),

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
  UNSUPPORTED_LANGUAGE_FEATURE (4005, ErrorLevel.UNDEFINED),

  /**
   * Standardized errors. These should cause a parse failure. They are
   * broadly grouped by topic.
   */

  // Basic errors
  SYMBOL_UNDEFINED (4200, ErrorLevel.ERROR),
  SYMBOL_REDEFINED (4201, ErrorLevel.ERROR),
  BUILT_IN_SYMBOL_REDEFINED (4202, ErrorLevel.ERROR),
  OPERATOR_NAME_INCOMPLETE (4203, ErrorLevel.ERROR),
  OPERATOR_GIVEN_INCORRECT_NUMBER_OF_ARGUMENTS (4204, ErrorLevel.ERROR),
  OPERATOR_LEVEL_CONSTRAINTS_EXCEEDED (4205, ErrorLevel.ERROR),
  ASSUMPTION_IS_NOT_CONSTANT (4206, ErrorLevel.ERROR),

  // Module import errors
  MODULE_FILE_CANNOT_BE_FOUND (4220, ErrorLevel.ERROR),
  MODULE_NAME_DIFFERENT_FROM_FILE_NAME (4221, ErrorLevel.ERROR),
  MODULE_DEPENDENCIES_ARE_CIRCULAR (4222, ErrorLevel.ERROR),
  MODULE_REDEFINED (4223, ErrorLevel.ERROR),
  EXTENDED_MODULES_SYMBOL_UNIFICATION_CONFLICT (4224, ErrorLevel.ERROR),

  // Instance substitution errors
  INSTANCE_SUBSTITUTION_MISSING_SYMBOL (4240, ErrorLevel.ERROR),
  INSTANCE_SUBSTITUTION_SYMBOL_REDEFINED_MULTIPLE_TIMES (4241, ErrorLevel.ERROR),
  INSTANCE_SUBSTITUTION_ILLEGAL_SYMBOL_REDEFINITION (4242, ErrorLevel.ERROR),
  INSTANCE_SUBSTITUTION_OPERATOR_CONSTANT_INCORRECT_ARITY (4243, ErrorLevel.ERROR),
  INSTANCE_SUBSTITUTION_NON_LEIBNIZ_OPERATOR (4244, ErrorLevel.ERROR),
  INSTANCE_SUBSTITUTION_LEVEL_CONSTRAINTS_EXCEEDED (4245, ErrorLevel.ERROR),
  INSTANCE_SUBSTITUTION_LEVEL_CONSTRAINT_NOT_MET (4246, ErrorLevel.ERROR),
  INSTANCE_SUBSTITUTION_COPARAMETER_LEVEL_CONSTRAINTS_EXCEEDED (4247, ErrorLevel.ERROR),

  // Function & record errors
  FUNCTION_GIVEN_INCORRECT_NUMBER_OF_ARGUMENTS (4260, ErrorLevel.ERROR),
  FUNCTION_EXCEPT_AT_USED_WHERE_UNDEFINED (4261, ErrorLevel.ERROR),
  RECORD_CONSTRUCTOR_FIELD_REDEFINITION (4262, ErrorLevel.ERROR),

  // Higher-order operator errors
  HIGHER_ORDER_OPERATOR_REQUIRED_BUT_EXPRESSION_GIVEN (4270, ErrorLevel.ERROR),
  HIGHER_ORDER_OPERATOR_ARGUMENT_HAS_INCORRECT_ARITY (4271, ErrorLevel.ERROR),
  HIGHER_ORDER_OPERATOR_PARAMETER_LEVEL_CONSTRAINT_NOT_MET (4272, ErrorLevel.ERROR),
  HIGHER_ORDER_OPERATOR_COPARAMETER_LEVEL_CONSTRAINTS_EXCEEDED (4273, ErrorLevel.ERROR),
  LAMBDA_OPERATOR_ARGUMENT_HAS_INCORRECT_ARITY (4274, ErrorLevel.ERROR),
  LAMBDA_GIVEN_WHERE_EXPRESSION_REQUIRED (4275, ErrorLevel.ERROR),

  // Recursive operator errors
  RECURSIVE_OPERATOR_PRIMES_PARAMETER (4290, ErrorLevel.ERROR),
  RECURSIVE_OPERATOR_DECLARED_BUT_NOT_DEFINED (4291, ErrorLevel.ERROR),
  RECURSIVE_OPERATOR_DECLARATION_DEFINITION_ARITY_MISMATCH (4292, ErrorLevel.ERROR),
  RECURSIVE_OPERATOR_DEFINED_IN_WRONG_LET_IN_LEVEL (4293, ErrorLevel.ERROR),
  RECURSIVE_SECTION_CONTAINS_ILLEGAL_DEFINITION (4294, ErrorLevel.ERROR),

  // Special-case operator level checking errors
  ALWAYS_PROPERTY_SENSITIVE_TO_STUTTERING (4310, ErrorLevel.ERROR),
  EVENTUALLY_PROPERTY_SENSITIVE_TO_STUTTERING (4311, ErrorLevel.ERROR),
  BINARY_TEMPORAL_OPERATOR_WITH_ACTION_LEVEL_PARAMETER (4312, ErrorLevel.ERROR),
  LOGICAL_OPERATOR_WITH_MIXED_ACTION_TEMPORAL_PARAMETERS (4313, ErrorLevel.ERROR),
  QUANTIFIED_TEMPORAL_FORMULA_WITH_ACTION_LEVEL_BOUND (4314, ErrorLevel.ERROR),
  QUANTIFICATION_WITH_TEMPORAL_LEVEL_BOUND (4315, ErrorLevel.ERROR),

  // Label errors
  LABEL_PARAMETER_REPETITION (4330, ErrorLevel.ERROR),
  LABEL_PARAMETER_MISSING (4331, ErrorLevel.ERROR),
  LABEL_PARAMETER_UNNECESSARY (4332, ErrorLevel.ERROR),
  LABEL_NOT_IN_DEFINITION_OR_PROOF_STEP (4333, ErrorLevel.ERROR),
  LABEL_NOT_ALLOWED_IN_NESTED_ASSUME_PROVE_WITH_NEW (4334, ErrorLevel.ERROR),
  LABEL_NOT_ALLOWED_IN_FUNCTION_EXCEPT (4335, ErrorLevel.ERROR),
  LABEL_REDEFINITION (4336, ErrorLevel.ERROR),
  LABEL_GIVEN_INCORRECT_NUMBER_OF_ARGUMENTS (4337, ErrorLevel.ERROR),

  // Proof-related errors
  PROOF_STEP_WITH_IMPLICIT_LEVEL_CANNOT_HAVE_NAME (4350, ErrorLevel.ERROR),
  PROOF_STEP_NON_EXPRESSION_USED_AS_EXPRESSION (4351, ErrorLevel.ERROR),
  TEMPORAL_PROOF_GOAL_WITH_NON_CONSTANT_TAKE_WITNESS_HAVE (4352, ErrorLevel.ERROR),
  TEMPORAL_PROOF_GOAL_WITH_NON_CONSTANT_CASE (4353, ErrorLevel.ERROR),
  QUANTIFIED_TEMPORAL_PICK_FORMULA_WITH_NON_CONSTANT_BOUND (4354, ErrorLevel.ERROR),
  ASSUME_PROVE_USED_WHERE_EXPRESSION_REQUIRED (4355, ErrorLevel.ERROR),
  ASSUME_PROVE_NEW_CONSTANT_HAS_TEMPORAL_LEVEL_BOUND (4356, ErrorLevel.ERROR),
  USE_OR_HIDE_FACT_NOT_VALID (4357, ErrorLevel.ERROR),

  /**
   * Standardized warnings. These should not cause a parse failure.
   */
  EXTENDED_MODULES_SYMBOL_UNIFICATION_AMBIGUITY (4800, ErrorLevel.WARNING),
  INSTANCED_MODULES_SYMBOL_UNIFICATION_AMBIGUITY (4801, ErrorLevel.WARNING),
  RECORD_CONSTRUCTOR_FIELD_NAME_CLASH (4802, ErrorLevel.WARNING),
  PLUSCAL_ALGORITHM_AND_TRANSLATION_CHANGED_SINCE_LAST_TRANSLATION (4803, ErrorLevel.WARNING),
  PLUSCAL_ALGORITHM_CHANGED_SINCE_LAST_TRANSLATION (4804, ErrorLevel.WARNING),
  PLUSCAL_TRANSLATION_CHANGED_SINCE_LAST_TRANSLATION (4805, ErrorLevel.WARNING);

  /**
   * The error's level of seriousness.
   */
  public static enum ErrorLevel {
    UNDEFINED,
    WARNING,
    ERROR
  }

  /**
   * The standardized error code value.
   */
  private final int value;

  /**
   * The error's level of seriousness.
   */
  private final ErrorLevel level;

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

  /**
   * Given the standardized error value, find and return the enum instance
   * to which it corresponds.
   *
   * @param value The standardized error value.
   * @return An enum corresponding to the given error value.
   */
  public static ErrorCode fromStandardValue(final int value) {
    final ErrorCode code = ErrorCode.codeMap.get(value);
    if (null == code) {
      throw new IllegalArgumentException(Integer.toString(value));
    }
    return code;
  }

  /**
   * Get the standardized error value of this error code enum.
   * @return The enum error code's standardized value.
   */
  public int getStandardValue() {
    return this.value;
  }

  /**
   * Get the {@link ErrorLevel} representing the severity of this error code.
   * @return The severity of this error code.
   */
  public ErrorLevel getSeverityLevel() {
    return this.level;
  }
}
