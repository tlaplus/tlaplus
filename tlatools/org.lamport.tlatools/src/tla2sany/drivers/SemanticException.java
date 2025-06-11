// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.drivers;

import tla2sany.semantic.AbortException;
import tla2sany.semantic.Errors;
import tla2sany.semantic.Errors.ErrorDetails;

/**
 * User-facing exception class for errors occurring during later stages
 * of the parse process. Translates internal-only {@link AbortException}
 * instances into external-ready {@link SemanticException} instances. For
 * errors occurring earlier during the syntax processing phase of the parse
 * process, consider using {@link tla2sany.parser.ParseException} instead.
 */
public class SemanticException extends Exception {

  /**
   * Initializes a new instance of the {@link SemanticException} class.
   *
   * @param internalException The internal exception causing the error.
   */
  public SemanticException(AbortException internalException) {
    super(internalException);
  }

  /**
   * Get details of the error that caused this exception, for programmatic
   * exception handling by parser clients.
   *
   * @return Details about the error that caused this exception.
   */
  public ErrorDetails getDetails() {
    return ((AbortException)this.getCause()).getDetails();
  }

  /**
   * Get error log to which the error causing this exception was reported.
   * Log will contain details of the error causing this exception and also
   * possibly other errors.
   *
   * @return Error log to which error causing this exception was reported.
   */
  public Errors getSourceErrorLog() {
    return ((AbortException)this.getCause()).getSourceErrorLog();
  }
}
