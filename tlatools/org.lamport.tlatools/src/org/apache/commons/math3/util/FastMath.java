package org.apache.commons.math3.util;

public class FastMath {

    public static double sqrt(final int d) {
        // The original implementation of FastMath.java in Apache Commons Math delegates
        // to Math.sqrt too. However, its FastMath has many more methods in that we drag
        // in many dependencies. We don't want nor need those dependencies.
        return Math.sqrt(d);
    }
}
