// Copyright (c) 2023, Oracle and/or its affiliates.

package tlc2.util;

/**
 * An enum for {@link #YES}, {@link #NO}, or {@link #MAYBE} (not all questions have definite answers).
 */
public enum PartialBoolean {
    YES,
    NO,
    MAYBE;

    public boolean isDefinitely(boolean value) {
        switch (this) {
            case YES:   return value;
            case NO:    return !value;
            case MAYBE: return false;
            default:
                // unreachable; necessary to satisfy javac
                throw new UnsupportedOperationException(this.toString());
        }
    }

    public boolean couldBe(boolean value) {
        return !isDefinitely(!value);
    }

}
