package org.lamport.tla.toolbox.distributed;

import java.io.IOException;
import java.net.URL;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

public abstract class URLHttpServlet extends HttpServlet {

	private static final long serialVersionUID = 1543293859269681164L;

	protected URL url;
	
	/* (non-Javadoc)
	 * @see javax.servlet.http.HttpServlet#doGet(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse)
	 */
	protected void doGet(final HttpServletRequest req, final HttpServletResponse resp) throws ServletException, IOException {
		// read the URL under which this servlet got accessed, assuming this is
		// the best hostname under which
		// the callee can access this host/servlet/resource
		final StringBuffer requestURL = req.getRequestURL();
		url = new URL(requestURL.toString());
	}
}
