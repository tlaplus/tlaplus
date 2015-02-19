
// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.xml;
import java.io.*;

/**
 * an exception for erroes in the exporter
 */

public class XMLExportingException extends Exception {
  private Exception nested;
  public XMLExportingException(String str, Exception n) {
    super(str);
    nested = n;
  }
  public Exception getNestedException() {
    return nested;
  }

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
