// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tlatools.impl.distributed;

import java.io.PipedOutputStream;
import java.io.PrintStream;

import util.ToolIO;

public class OSGiPrintStream extends PrintStream {

	private final String prefix;

	public OSGiPrintStream(final String prefix) {
		super(new PipedOutputStream());
		this.prefix = prefix + ": ";
		ToolIO.out = this;
		ToolIO.err = this;
	}

	/* (non-Javadoc)
	 * @see java.io.PrintStream#print(java.lang.String)
	 */
	public void print(String str) {
		System.out.print(prefix + str);
	}

	/* (non-Javadoc)
	 * @see java.io.PrintStream#println(java.lang.String)
	 */
	public void println(String str) {
		System.out.println(prefix + str);
	}
}
