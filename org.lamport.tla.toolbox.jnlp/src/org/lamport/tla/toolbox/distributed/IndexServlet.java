// Copyright (c) 2011 Microsoft Corporation. All rights reserved.
package org.lamport.tla.toolbox.distributed;

import java.io.IOException;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

public class IndexServlet extends URLHttpServlet {

	private static final long serialVersionUID = -653938914619406447L;
	private static final String TLA2TOOLS_JAR = "tla2tools.jar";

	/* (non-Javadoc)
	 * @see javax.servlet.http.HttpServlet#doGet(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse)
	 */
	@Override
	protected void doGet(final HttpServletRequest req, final HttpServletResponse resp) throws ServletException, IOException {
		super.doGet(req, resp);
		
		resp.setContentType("text/html");
		
		resp.getWriter().println("<!DOCTYPE html>");

		resp.getWriter().println(
				"<html><head>\n" + 
						"<title>Distributed TLC</title>\n" + 
				"</head>");
		
		// boostrap JRE on Windows systems
		resp.getWriter().println(
				"<object codebase=\"https://java.sun.com/update/1.7.0/jinstall-7u55-windows-i586.cab#Version=7,0,0,0\" classid=\"clsid:5852F5ED-8BF4-11D4-A245-0080C6F74284\" height='0' width='0'>" +
						"<param name=\"app\" value=\"" + url + "\"/>" +
						"<param name=\"back\" value=\"false\"/>" +
				"</object>");
		
		// first table
		printTable(resp, JNLPGeneratorServlet.JNLP, JNLPGeneratorServlet.MAINCLASS, "worker", JNLPGeneratorServlet.INDEX_DESC);

		// second table
		printTable(resp, FPSetJNLPGeneratorServlet.JNLP, FPSetJNLPGeneratorServlet.MAINCLASS, "fingerprint set", FPSetJNLPGeneratorServlet.INDEX_DESC);
		
		// third table
		printTable(resp, CombinedJNLPGeneratorServlet.JNLP, CombinedJNLPGeneratorServlet.MAINCLASS, "combined", CombinedJNLPGeneratorServlet.INDEX_DESC);
		
		resp.getWriter().println(
				"</body></html>");
	}

	private void printTable(final HttpServletResponse resp, final String jnlpName, final String mainClass, final String name, final String description) throws IOException {
		resp.getWriter().println(
				"<table id=\"header\" cellpadding=\"0\" cellspacing=\"0\" width=\"100%\" border=\"0\">\n" + 
					"<p>" + description + "</p>\n" + 
					"<tr><td>\n" + 
					"<ul>");
			
		// a) fpset direct link
		resp.getWriter().println(
				"<li>\n" + 
						"<p><a href=\"" + jnlpName + "\" id=\"jnlp-link\"><img alt=\"launch FPSet\" src=\"/files/webstart.gif\" /> Launch "
								+ name + " from browser</a></p>\n" + 
				"</li>");
		
		// b) command line
		resp.getWriter().println(
				"<li>\n" + 
					"<p>Run from slave command line:</p>\n" + 
					"<p><pre>" + 
						"javaws " + url + jnlpName +
					"</pre></p>\n" + 
				"</li>");
		
		// c) headless
		resp.getWriter().println(
				"<li>\n" + 
					"<p>Or if the slave is headless:</p>\n" + 
					"<pre>\n" + 
						"wget " + addr + "/files/" + TLA2TOOLS_JAR + "\n" + 
						"java -cp <a href=\"/files/" + TLA2TOOLS_JAR + "\">" + TLA2TOOLS_JAR + "</a> " + mainClass
						+ " " + url.getHost() +
					"</pre>\n" + 
				"</li>");
		
		resp.getWriter().println(
				"</ul>\n" + 
				"</td></tr></table>\n");
	}
}
