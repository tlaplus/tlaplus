// Copyright (c) 2025, Oracle and/or its affiliates.

package tlc2.tool.impl;

import tla2sany.semantic.SemanticNode;
import tlc2.util.Context;

/**
 * Information about an invariant violation.  This class has no particular structure, only a single
 * {@link #formatPretty()} method to display the information.  Today it shows a location of a relevant FALSE
 * expression and the values of any {@code \A}-bound variables.
 */
public class InvariantViolation {

    public static final InvariantViolation NO_VIOLATION = null;

    private final SemanticNode subexpression;
    private final Context context;

    public InvariantViolation(SemanticNode subexpression, Context context) {
        this.subexpression = subexpression;
        this.context = context;
    }

    public String formatPretty() {
        StringBuilder sb = new StringBuilder();
        sb.append("The expression at ")
                .append(subexpression)
                .append(" is FALSE");

        Context ptr = context;
        if (ptr != Context.Empty) {
            sb.append(" (when ");
            boolean first = true;
            do {
                if (first) {
                    first = false;
                } else {
                    sb.append(", ");
                }
                sb.append(ptr.getName().getName()).append(" = ").append(ptr.getValue());
                ptr = ptr.next();
            } while (ptr != Context.Empty);
            sb.append(')');
        }

        return sb.toString();
    }

    @Override
    public String toString() {
        return "InvariantViolation{" +
                "subexpression=" + subexpression +
                ", context=" + context +
                '}';
    }

}
