// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package org.lamport.tla.toolbox.distributed;

@SuppressWarnings("serial")
public class FPSetJNLPGeneratorServlet extends JNLPGeneratorServlet {
	
	public static final String JNLP = "fpset.jnlp";
	public static final String DESCRIPTION = "Distributed TLC fingerprint set";
	public static final String INDEX_DESC = "Start a fingerprint (FPSet) server:";
	public static final String MAINCLASS = "tlc2.tool.distributed.fp.DistributedFPSet";

	public FPSetJNLPGeneratorServlet() {
		super(MAINCLASS, DESCRIPTION, JNLP);
	}
}
