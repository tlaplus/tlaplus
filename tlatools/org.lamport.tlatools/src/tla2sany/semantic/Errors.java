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

  private List<String> warnings = new ArrayList<String>();
  private List<String> errors   = new ArrayList<String>();
  private List<String> aborts   = new ArrayList<String>();

  /*************************************************************************
  * The following methods to return the warnings, errors, and aborts in a  *
  * sane way were added by LL on 12 May 2008.                              *
  *************************************************************************/
  public String[] getAborts()   { return this.aborts.toArray(String[]::new); }
  public String[] getErrors()   { return this.errors.toArray(String[]::new); }
  public String[] getWarnings() { return this.warnings.toArray(String[]::new); }

  public final void addWarning( Location loc, String str ) {
    if (loc == null) loc = Location.nullLoc;
    final String message = loc.toString() + "\n\n" + str;
    if (!this.warnings.contains(message)) {
      this.warnings.add(message);
    }
  }

  public final void addError(Location loc, String str) {
    if (loc == null) loc = Location.nullLoc;
    final String message = loc.toString() + "\n\n" + str;
    if (!this.errors.contains(message)) {
      this.errors.add(message);
    }
  }

  /**
   * 
   * @param loc
   * @param str
   * @param abort throw an abort exception iff true 
   * @throws AbortException
   */
  public final void addAbort(Location loc, String str, boolean abort) throws AbortException {
    if (loc == null) loc = Location.nullLoc;
    final String message = loc.toString() + "\n\n" + str;
    if (!this.aborts.contains(message)) {
      this.aborts.add(message);
    }

    if (abort){
      throw new AbortException();
    }
  }

  public final void addAbort(Location loc, String str ) throws AbortException {
    addAbort(loc, str, true);
  }


  public final void addAbort(String str, boolean abort) throws AbortException {
    addAbort(Location.nullLoc, str, abort);
  }


  public final void addAbort(String str) throws AbortException {
    addAbort(Location.nullLoc, str, true);
  }

  public final boolean isSuccess()             { return this.aborts.isEmpty() && this.errors.isEmpty(); }

  public final boolean isFailure()             { return !this.isSuccess(); }

  public final int     getNumErrors()          { return this.errors.size(); }

  public final int     getNumAbortsAndErrors() { return this.aborts.size() + this.errors.size(); }

  public final int     getNumMessages()        { return this.aborts.size() + this.errors.size() + this.warnings.size(); }

  public final String  toString()  {
    StringBuffer ret = new StringBuffer("");

    ret.append((this.aborts.size() > 0) ? "*** Abort messages: " + this.aborts.size() + "\n\n" : "");
    for (final String message : this.aborts)   {
      ret.append(message + "\n\n\n");
    }

    ret.append((this.errors.size() > 0) ? "*** Errors: " + this.errors.size() + "\n\n" : "");
    for (final String message : this.errors)   {
      ret.append(message + "\n\n\n");
    }

    ret.append((this.warnings.size() > 0) ? "*** Warnings: " + this.warnings.size() + "\n\n" : "");
    for (final String message : this.warnings) {
      ret.append(message + "\n\n\n");
    }

    return ret.toString();
  }
}
