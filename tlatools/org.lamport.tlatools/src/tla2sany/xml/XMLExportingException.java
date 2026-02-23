
// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.xml;
import java.io.PrintWriter;
import java.io.StringWriter;

/**
 * An exception wrapper class for errors occurring during execution of
 * {@link XMLExporter}.
 */
public class XMLExportingException extends Exception {

  /**
   * The standardized error code attached to this exception.
   */
  private final XMLExporterExitCode code;

  /**
   * The inner exception wrapped by this exception.
   */
  private final Exception nested;

  public XMLExportingException(XMLExporterExitCode code, String str, Exception nested) {
    super(str);
    this.nested = nested;
    this.code = code;
  }

  /**
   * Get the nested exception that originally caused the failure.
   */
  public Exception getNestedException() {
    return nested;
  }

  /**
   * Get the standardized error code attached to this failure.
   */
  public XMLExporterExitCode code() {
    return this.code;
  }

  @Override
  public String toString() {
    if (nested == null)
      return super.toString();
    else {
      StringWriter sw = new StringWriter();
      nested.printStackTrace(new PrintWriter(sw));
      return super.toString() + "\n" + sw.toString();
    }
  }
}
