// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tlatools.impl.distributed;

import java.io.PrintStream;

import util.ToolIO;

public abstract class TLCWrapper {

	public void connect(String string) {
		PrintStream ps = new OSGiPrintStream(string);
		ToolIO.err = ps;
		ToolIO.out = ps;
	}
}
