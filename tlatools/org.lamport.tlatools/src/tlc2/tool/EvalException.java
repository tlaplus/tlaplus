// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:27:18 PST by lamport
//      modified on Thu Dec  7 20:32:45 PST 2000 by yuanyu

package tlc2.tool;

import tlc2.output.MP;

/**
 * Evaluation exception
 *
 * @author Simon Zambrovski
 * @version $Id$
 */
public class EvalException extends StatefulRuntimeException {
// SZ Jul 14, 2009: not used since error codes are in the {@link EC} class


    private static final long serialVersionUID = -7401139507774908329L;
    private final int errorCode;
    private final String[] parameters;

    public EvalException(final int errorCode, final String[] parameters) {
        super(MP.getMessage(errorCode, parameters));
        this.errorCode = errorCode;
        this.parameters = parameters;
    }

    public EvalException(final int errorCode, final String parameter) {
        this(errorCode, new String[]{parameter});
    }

    public EvalException(final int errorCode) {
        super(MP.getMessage(errorCode));
        this.errorCode = errorCode;
        this.parameters = null;
    }

    public int getErrorCode() {
        return errorCode;
    }

    public String[] getParameters() {
        return parameters;
    }

    public boolean hasParameters() {
        return parameters != null;
    }
}
