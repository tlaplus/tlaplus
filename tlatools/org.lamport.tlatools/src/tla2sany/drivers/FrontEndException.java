// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.drivers;

/**
 * Exception thrown by SANY on errors
 * @author Leslie Lamport
 */
public class FrontEndException extends Exception {
    // SZ Feb 20, 2009: fixed the exception chaining
    // instead of having the cause as a member, the 
    // exception now has it in trace
    // also changed the visibility to public
	public FrontEndException(final Exception cause) {
		super(cause);
    }
    
    public FrontEndException(final String msg) {
    	super(msg);
    }
}
