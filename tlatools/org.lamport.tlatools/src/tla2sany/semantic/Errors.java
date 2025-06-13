// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

/***************************************************************************
* Every Semantic node has an errors field that is an Errors object.  A     *
* SpecObj object also has a few different kinds of Errors objects.  Here   *
* are the relevant methods:                                                *
*                                                                          *
*    addWarning                                                            *
*    addError                                                              *
*    addAbort   : These methods add the indicated level of error.          *
*                                                                          *
*    isSuccess()                                                           *
*    isFailure() : Indicates if addError or addAbort was called.           *
*                                                                          *
*    getNumErrors()                                                        *
*    getNumAbortsAndErrors()                                               *
*    getNumMessages()        : Return approximately obvious values.        *
*                                                                          *
*    toString() : Returns all the errors as a single string.               *
***************************************************************************/
package tla2sany.semantic;

import java.util.ArrayList;
import java.util.List;

import tla2sany.st.Location;

public class Errors {

  public static class ErrorDetails {

    private final ErrorCode code;

    private final Location location;

    private final String message;

    public ErrorDetails(ErrorCode code, Location location, String message) {
      this.code = code;
      this.location = location;
      this.message = message;
    }

    public ErrorCode getCode() {
      return this.code;
    }

    public Location getLocation() {
      return this.location;
    }

    public String getMessage() {
      return this.message;
    }

    @Override
    public String toString() {
      return this.location.toString() + "\n\n" + this.message;
    }

    @Override
    public boolean equals(Object o) {
      if (!(o instanceof ErrorDetails)) {
        return false;
      }
      final ErrorDetails other = (ErrorDetails)o;
      return this.code.equals(other.code)
          && this.location.equals(other.location)
          && this.message.equals(other.message);
    }
  }

  private List<ErrorDetails> warnings = new ArrayList<ErrorDetails>();
  private List<ErrorDetails> errors   = new ArrayList<ErrorDetails>();

  public String[] getErrors()   { return this.errors.stream().map(ErrorDetails::toString).toArray(String[]::new); }
  public String[] getWarnings() { return this.warnings.stream().map(ErrorDetails::toString).toArray(String[]::new); }

  public List<ErrorDetails> getErrorDetails()   { return new ArrayList<ErrorDetails>(this.errors); }
  public List<ErrorDetails> getWarningDetails() { return new ArrayList<ErrorDetails>(this.warnings); }

  public final void addWarning(ErrorCode code, Location loc, String str) {
    if (loc == null) {
      loc = Location.nullLoc;
    }
    final ErrorDetails error = new ErrorDetails(code, loc, str);
    if (!this.warnings.contains(error)) {
      this.warnings.add(error);
    }
  }

  public final AbortException addError(ErrorCode code, Location loc, String str) {
    if (loc == null) {
      loc = Location.nullLoc;
    }
    final ErrorDetails error = new ErrorDetails(code, loc, str);
    if (!this.errors.contains(error)) {
      this.errors.add(error);
    }
    
    return new AbortException();
  }

  public final boolean isSuccess()             { return this.errors.isEmpty(); }

  public final boolean isFailure()             { return !this.isSuccess(); }

  public final int     getNumErrors()          { return this.errors.size(); }

  public final int     getNumMessages()        { return this.errors.size() + this.warnings.size(); }

  public final String  toString()  {
    StringBuffer ret = new StringBuffer("");

    ret.append((this.errors.size() > 0) ? "*** Errors: " + this.errors.size() + "\n\n" : "");
    for (final ErrorDetails error : this.errors)   {
      ret.append(error.toString() + "\n\n\n");
    }

    ret.append((this.warnings.size() > 0) ? "*** Warnings: " + this.warnings.size() + "\n\n" : "");
    for (final ErrorDetails error : this.warnings) {
      ret.append(error.toString() + "\n\n\n");
    }

    return ret.toString();
  }
}
