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

import tla2sany.st.Location;
import tla2sany.utilities.Vector;


public class Errors {

  private boolean succeed = true;

  private int    numAborts   = 0;
  private int    numErrors   = 0;
  private int    numWarnings = 0;

  private Vector warnings = new Vector();
  private Vector errors   = new Vector();
  private Vector aborts   = new Vector();

  /*************************************************************************
  * The following methods to return the warnings, errors, and aborts in a  *
  * sane way were added by LL on 12 May 2008.                              *
  *************************************************************************/
  public String[] getAborts()   { return StringVectortoStringArray(aborts) ; }
  public String[] getErrors()   { return StringVectortoStringArray(errors) ; }
  public String[] getWarnings() { return StringVectortoStringArray(warnings) ; }

  private String[] StringVectortoStringArray(Vector vec) {
    String[] retVal = new String[vec.size()] ;
    for (int i = 0 ; i < retVal.length; i++) {
      retVal[i] = (String) vec.elementAt(i) ;
     } ;
    return retVal;
   }

  public final void addWarning( Location loc, String str ) { 
    if (loc == null) loc = Location.nullLoc;

    int i;
    for (i = warnings.size()-1; i >= 0; i--) {
      if ( (loc.toString() + "\n\n" + str).equals( warnings.elementAt(i) ) ) break;
    }

    if ( i < 0) {
      warnings.addElement( loc.toString() + "\n\n"+ str );
      numWarnings++;
    }
  }


  public final void addError(Location loc, String str) {
    if (loc == null) loc = Location.nullLoc;

    int i;
    for (i = errors.size()-1; i >= 0; i--) {
      if ( (loc.toString() + "\n\n" + str).equals( errors.elementAt(i) ) )  break;
    }

    if ( i < 0) {
      errors.addElement( loc.toString() + "\n\n"+ str );
      numErrors++;
    }
    succeed = false;

  }
  

  /**
   * 
   * @param loc
   * @param str
   * @param abort throw an abort exception iff true 
   * @throws AbortException
   */
  public final void addAbort(Location loc, String str, boolean abort) throws AbortException {
    String errMsg = loc.toString() + "\n\n" + str;
    int i;
    for (i = aborts.size()-1; i >= 0; i--) {
      if (errMsg.equals(aborts.elementAt(i))) break;
    }
    if (i < 0) {
      aborts.addElement(errMsg);
      numAborts++;
    }
    succeed = false;

    if (abort){
      // System.out.println(this.toString());
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

  public final boolean isSuccess()             { return succeed; }

  public final boolean isFailure()             { return !succeed; }

  public final int     getNumErrors()          { return numErrors; }

  public final int     getNumAbortsAndErrors() { return numAborts + numErrors; }

  public final int     getNumMessages()        { return numAborts + numErrors + numWarnings; }

  public final String  toString()  { 
    StringBuffer ret = new StringBuffer("");

    ret.append((numAborts > 0) ? "*** Abort messages: " + numAborts + "\n\n" : "");
    for (int i = 0; i < aborts.size(); i++)   {
      ret.append(aborts.elementAt(i) + "\n\n\n");
    }

    ret.append((numErrors > 0) ? "*** Errors: " + numErrors + "\n\n" : "");
    for (int i = 0; i < errors.size(); i++)   {
      ret.append(errors.elementAt(i) + "\n\n\n");
    }

    ret.append((numWarnings > 0) ? "*** Warnings: " + numWarnings + "\n\n" : "");
    for (int i = 0; i < warnings.size(); i++) {
      ret.append(warnings.elementAt(i) + "\n\n\n");
    }

    return ret.toString();
  }
	    
}
