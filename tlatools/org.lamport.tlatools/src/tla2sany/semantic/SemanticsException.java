// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

// This class is not used in the current code

public class SemanticsException extends Exception {

  int    severity;      // 0 == warning; 1 == error; 2 == abort
  String message;       // human-readable error message

  public SemanticsException( int s, String m) { 
    severity = s;
    message = m; 
  }

  public int    getSeverity() { return severity; }
  public String getMessage()  { return message; }

}
