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

import java.util.ArrayList;


public class Errors {

    private final ArrayList<String> warnings = new ArrayList<>();
    private final ArrayList<String> errors = new ArrayList<>();
    private final ArrayList<String> aborts = new ArrayList<>();
    private boolean succeed = true;
    private int numAborts = 0;
    private int numErrors = 0;
    private int numWarnings = 0;

    /*************************************************************************
     * The following methods to return the warnings, errors, and aborts in a  *
     * sane way were added by LL on 12 May 2008.                              *
     *************************************************************************/
    public String[] getAborts() {
        return StringArrayListtoStringArray(aborts);
    }

    public String[] getErrors() {
        return StringArrayListtoStringArray(errors);
    }

    public String[] getWarnings() {
        return StringArrayListtoStringArray(warnings);
    }

    private String[] StringArrayListtoStringArray(final ArrayList<String> vec) {
        final String[] retVal = new String[vec.size()];
        for (int i = 0; i < retVal.length; i++) {
            retVal[i] = vec.get(i);
        }
        return retVal;
    }

    public final void addWarning(Location loc, final String str) {
        if (loc == null) loc = Location.nullLoc;

        int i;
        for (i = warnings.size() - 1; i >= 0; i--) {
            if ((loc + "\n\n" + str).equals(warnings.get(i))) break;
        }

        if (i < 0) {
            warnings.add(loc + "\n\n" + str);
            numWarnings++;
        }
    }


    public final void addError(Location loc, final String str) {
        if (loc == null) loc = Location.nullLoc;

        int i;
        for (i = errors.size() - 1; i >= 0; i--) {
            if ((loc + "\n\n" + str).equals(errors.get(i))) break;
        }

        if (i < 0) {
            errors.add(loc + "\n\n" + str);
            numErrors++;
        }
        succeed = false;

    }


    /**
     * @param abort throw an abort exception iff true
     */
    public final void addAbort(final Location loc, final String str, final boolean abort) throws AbortException {
        final String errMsg = loc.toString() + "\n\n" + str;
        int i;
        for (i = aborts.size() - 1; i >= 0; i--) {
            if (errMsg.equals(aborts.get(i))) break;
        }
        if (i < 0) {
            aborts.add(errMsg);
            numAborts++;
        }
        succeed = false;

        if (abort) {
            // System.out.println(this.toString());
            throw new AbortException();
        }
    }

    public final void addAbort(final Location loc, final String str) throws AbortException {
        addAbort(loc, str, true);
    }


    public final void addAbort(final String str, final boolean abort) throws AbortException {
        addAbort(Location.nullLoc, str, abort);
    }


    public final void addAbort(final String str) throws AbortException {
        addAbort(Location.nullLoc, str, true);
    }

    public final boolean isSuccess() {
        return succeed;
    }

    public final boolean isFailure() {
        return !succeed;
    }

    public final int getNumErrors() {
        return numErrors;
    }

    public final int getNumAbortsAndErrors() {
        return numAborts + numErrors;
    }

    public final int getNumMessages() {
        return numAborts + numErrors + numWarnings;
    }

    public final String toString() {
        final StringBuilder ret = new StringBuilder();

        ret.append((numAborts > 0) ? "*** Abort messages: " + numAborts + "\n\n" : "");
        for (String abort : aborts) {
            ret.append(abort).append("\n\n\n");
        }

        ret.append((numErrors > 0) ? "*** Errors: " + numErrors + "\n\n" : "");
        for (String error : errors) {
            ret.append(error).append("\n\n\n");
        }

        ret.append((numWarnings > 0) ? "*** Warnings: " + numWarnings + "\n\n" : "");
        for (String warning : warnings) {
            ret.append(warning).append("\n\n\n");
        }

        return ret.toString();
    }

}
