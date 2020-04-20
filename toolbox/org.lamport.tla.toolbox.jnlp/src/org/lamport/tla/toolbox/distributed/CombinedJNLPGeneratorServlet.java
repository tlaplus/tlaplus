// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package org.lamport.tla.toolbox.distributed;

/**
 * Serves the JNLP file for the fingerprint server & TLC worker combination.
 * 
 * Beginning with 1.7.0 we ceased supporting JNLP, due to our move to Java 11. Until a contributor arrives to take over
 * this functionality, including providing a nice way to bundle IcedTea or similar with the Toolbox, i am marking this
 * class as deprecated.
 * 
 * @deprecated
 */
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
