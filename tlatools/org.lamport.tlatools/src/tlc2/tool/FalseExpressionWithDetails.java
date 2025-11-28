// Copyright (c) 2025, Oracle and/or its affiliates.

package tlc2.tool;

import tla2sany.semantic.SemanticNode;
import tlc2.util.Context;

/**
 * Information about an expression that evaluated to FALSE with details about why.  This class has no particular
 * publicly-exposed structure, only a single {@link #prettyPrint()} method to display the information.
 */
public class FalseExpressionWithDetails {

    /**
     * Alias for {@code null}, used if an expression was actually true instead of false.  This constant provides
     * a slightly more readable name than using {@code null} directly.
     */
    public static final FalseExpressionWithDetails NO_VIOLATION = null;

    private final SemanticNode subexpression;
    private final Context context;

    public FalseExpressionWithDetails(SemanticNode subexpression, Context context) {
        this.subexpression = subexpression;
        this.context = context;
    }

    public String prettyPrint() {
        StringBuilder sb = new StringBuilder();
        sb.append("The first false conjunct was: ").append(subexpression);

        Context ptr = context;
        if (ptr != Context.Empty) {
            sb.append("\nValues of \\A-bound names: ");
            while (ptr != Context.Empty) {
                sb.append("\n    ")
                        .append(ptr.getName().getName())
                        .append(" = ")
                        .append(ptr.getValue());
                ptr = ptr.next();
            }
        }

        return sb.toString();
    }

    @Override
    public String toString() {
        return "FalseExpressionWithDetails{" +
                "subexpression=" + subexpression +
                ", context=" + context +
                '}';
    }

}
