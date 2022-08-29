// Copyright (c) 2013 INRIA-MSR.  All rights reserved.

package tla2sany.xml;

import java.io.PrintWriter;
import java.io.StringWriter;

/**
 * an exception for erroes in the exporter
 */

public class XMLExportingException extends Exception {
    private static final long serialVersionUID = -8894858605017149534L;
    private final Exception nested;

    public XMLExportingException(final String str, final Exception n) {
        super(str);
        nested = n;
    }

    public Exception getNestedException() {
        return nested;
    }

    @Override
    public String toString() {
        if (nested == null)
            return super.toString();
        else {
            final StringWriter sw = new StringWriter();
            nested.printStackTrace(new PrintWriter(sw));
            return super.toString() + "\n" + sw;
        }
    }
}
