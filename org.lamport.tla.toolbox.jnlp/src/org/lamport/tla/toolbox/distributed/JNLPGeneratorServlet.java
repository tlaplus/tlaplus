// Copyright (c) 2011 Microsoft Corporation. All rights reserved.
package org.lamport.tla.toolbox.distributed;

import java.io.IOException;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

/**
 * Serves the {@link tlc2.tool.distributed.TLCWorker} jnlp file
 */
public class JNLPGeneratorServlet extends URLHttpServlet {

	public static final String MAINCLASS = "tlc2.tool.distributed.TLCWorker";
	public static final String DESCRIPTION = "Distributed TLC worker instance";
	public static final String INDEX_DESC = "Connect to TLCworker one of these ways:";
	public static final String JNLP = "worker.jnlp";

	protected final String mainClass;
	protected final String description;
	public final String servletName;

	private static final long serialVersionUID = 6158685065128002088L;
	
	public JNLPGeneratorServlet() {
		this(MAINCLASS, DESCRIPTION, JNLP);
	}
	
	public JNLPGeneratorServlet(String mainClass, String description, String servletName) {
		this.mainClass = mainClass;
		this.description = description;
		this.servletName = servletName;
	}
	
	/* (non-Javadoc)
	 * @see javax.servlet.http.HttpServlet#doGet(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse)
	 */
	@Override
	protected void doGet(final HttpServletRequest req, final HttpServletResponse resp) throws ServletException, IOException {
		super.doGet(req, resp);
		
		resp.setContentType("application/x-java-jnlp-file");
		
		resp.getWriter().println(
				"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" + 
				"<jnlp codebase=\"" + addr + "\" href=\"" + servletName + "\">\n" +
					"<information>\n" + 
						"<title>" + mainClass + "</title>\n" + 
						"<vendor>Microsoft Corp.</vendor>\n" + 
						"<homepage href=\"http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html\"/>\n" + 
						"<description>" + description + "</description>\n" + 
					"</information>\n" + 
					"<security>\n" + 
						"<all-permissions/>\n" + 
					"</security>\n" + 
					"<resources>\n" + 
						"<j2se version=\"1.5+\"/>\n" + 
						"<jar href=\""+ addr + "/files/tla2tools.jar\"/>\n" + 
						//"<property name\"key\" value=\"value\"/>\n" + 
					"</resources>\n" + 
					"<application-desc main-class=\"" + mainClass + "\">\n" + 
						"<argument>" + url.getHost() + "</argument>\n" + 
					"</application-desc>\n" + 
				"</jnlp>");
	}
}
    