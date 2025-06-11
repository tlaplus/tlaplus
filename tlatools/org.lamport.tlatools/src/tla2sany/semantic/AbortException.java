// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import tla2sany.semantic.Errors.ErrorDetails;

/**
 * Exception thrown when an unrecoverable error occurs at some stage of
 * parsing. If your error is recoverable in a way that will not corrupt
 * further stages of the parse process, simply log it in the {@link Errors}
 * class instead; it is useful to the user to find as many errors as possible
 * during each run of the parser, although this is in tension with the
 * tendency of parse errors to beget additional subsequent parse errors.
 *
 * By convention {@link AbortException} is an internal exception, and it is
 * transformed into a {@link SemanticException} before propagating it up to
 * users.
 *
 * To ensure correct logging, should be created exclusively by calling
 * {@link Errors#addAbort(ErrorCode, tla2sany.st.Location, String, boolean)}.
 */
public class AbortException extends Exception {

  /**
   * Details about the error that caused this exception.
   */
  private final ErrorDetails details;
  
  /**
   * The error log to which the error was initially reported;
   */
  private final Errors sourceErrorLog;

  /**
   * Constructs a new instance of the {@link AbortException} class.
   *
   * @param details Details about the error that caused this exception.
   * @param sourceErrorLog Error log to which the error was reported.
   */
  public AbortException(ErrorDetails details, Errors sourceErrorLog) {
    this.details = details;
    this.sourceErrorLog = sourceErrorLog;
  }

  /**
   * Get details of the error that caused this exception, for programmatic
   * exception handling by parser clients.
   *
   * @return Details about the error that caused this exception.
   */
  public ErrorDetails getDetails() {
    return this.details;
  }
  
  /**
   * Get error log to which the error causing this exception was initially
   * reported. The log will possibly contain other errors and warnings in
   * addition to the one causing this exception.
   *
   * @return Error log instance to which this error was initially reported.
   */
  public Errors getSourceErrorLog() {
    return this.sourceErrorLog;
  }

  @Override
  public String toString() {
    return this.details.toString();
  }
}
