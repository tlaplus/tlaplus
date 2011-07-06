package org.lamport.tla.toolbox.distributed;

import java.io.IOException;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

public class IndexServlet extends URLHttpServlet {

	private static final String TLA2TOOLS_JAR = "tla2tools.jar";
	private static final long serialVersionUID = -653938914619406447L;

	/* (non-Javadoc)
	 * @see javax.servlet.http.HttpServlet#doGet(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse)
	 */
	@Override
	protected void doGet(final HttpServletRequest req, final HttpServletResponse resp) throws ServletException, IOException {
		super.doGet(req, resp);
		
		resp.setContentType("text/html");

		resp.getWriter().println(
				"<html><head>\n" + 
						"<title>TLCWorker</title>\n" + 
				"</head>\n" + 
				"<body>\n" + 
					"<table id=\"header\" cellpadding=\"0\" cellspacing=\"0\" width=\"100%\" border=\"0\">\n" + 
						"<p>Connect to TLCworker one of these ways:</p>\n" + 
						"<tr><td>\n" + 
						"<ul>");

		// a) direct link
		resp.getWriter().println(
				"<li><p>\n" + 
						"<a href=\"" + JNLPGeneratorServlet.SERVLET_NAME + "\" id=\"jnlp-link\"><img alt=\"launch worker\" src=\"/files/webstart.gif\" /> Launch worker from browser</a>\n" + 
				"</p></li>");

		// b) command line
		resp.getWriter().println(
				"<li><p>\n" + 
					"Run from slave command line:</p>\n" + 
					"<pre>\n" + 
						"javaws " + url + JNLPGeneratorServlet.SERVLET_NAME +
					"</pre>\n" + 
				"</p></li>");
		
		// c) headless
		resp.getWriter().println(
				"<li><p>\n" + 
					"Or if the slave is headless:</p>\n" + 
					"<pre>\n" + 
						"java -jar <a href=\"/" + TLA2TOOLS_JAR + "\">" + TLA2TOOLS_JAR + "</a> -jnlpUrl "
						+ url + JNLPGeneratorServlet.SERVLET_NAME +
					"</pre>\n" + 
				"</p></li>");
		
		resp.getWriter().println(
				"</ul>\n" + 
				"</td></tr></table>\n" + 
				"</body></html>");
	}
}
