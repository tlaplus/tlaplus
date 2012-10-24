// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package org.lamport.tla.toolbox.distributed;

@SuppressWarnings("serial")
public class CombinedJNLPGeneratorServlet extends JNLPGeneratorServlet {

	public static final String JNLP = "combined.jnlp";
	public static final String MAINCLASS = "tlc2.tool.distributed.fp.TLCWorkerAndFPSet";
	public static final String DESCRIPTION = "A combined fingerprint server (FPSet) and a TLCWorker";
	public static final String INDEX_DESC = "Start a combined fingerprint server (FPSet) and a TLCWorker";

	public CombinedJNLPGeneratorServlet() {
		super(MAINCLASS, DESCRIPTION, JNLP);
	}
}
