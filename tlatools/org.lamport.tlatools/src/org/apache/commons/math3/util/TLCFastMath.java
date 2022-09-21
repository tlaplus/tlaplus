package org.apache.commons.math3.util;

public class TLCFastMath {

	public static double sqrt(int d) {
		// The original implementation of FastMath.java in Apache Commons Math delegates
		// to Math.sqrt too. However, its FastMath has many more methods in that we drag
		// in many dependencies. We don't want nor need those dependencies.
		return Math.sqrt(d);
	}
	
    public static int abs(final int x) {
        return Math.abs(x);
    }
    
    public static int min(final int a, final int b) {
        return Math.min(a, b);
    }
}
