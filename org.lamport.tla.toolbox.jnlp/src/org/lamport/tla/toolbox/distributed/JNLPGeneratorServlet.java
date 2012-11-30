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

	public static final String SYS_PROPS = "sysprops";
	public static final String VM_ARGS = "vmargs";
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
						"<j2se version=\"1.5+\" " + getVMArgs(req) + "/>\n" + 
						"<jar href=\""+ addr + "/files/tla2tools.jar\"/>\n" + 
						//"<property name=\"key\" value=\"value\"/>\n" +
						getSystemProperties(req) + "\n" +
					"</resources>\n" + 
					"<application-desc main-class=\"" + mainClass + "\">\n" + 
						"<argument>" + url.getHost() + "</argument>\n" + 
					"</application-desc>\n" + 
					"" + 
				"</jnlp>");
	}

	/**
	 * Reads system properties from the query part of the remote request. A request looks like:
	 * 
	 * <pre>
	 * <code>http://localhost:10996/worker.jnlp?sysprops=-Dfoo.bar=5%20-Dfrob=2</code>
	 * </pre>
	 * 
	 * @see JNLPGeneratorServlet#getVMArgs(HttpServletRequest)
	 * @param req
	 *            The {@link HttpServletRequest} representing the user defined
	 *            url with a query part if any.
	 * @return The empty string if no query part for
	 *         {@link JNLPGeneratorServlet#SYS_PROPS} is given or a formatted
	 *         string of system properties.
	 */
	private String getSystemProperties(HttpServletRequest req) {
		final String sysProps = req.getParameter(SYS_PROPS);
		if (sysProps != null && !"".equalsIgnoreCase(sysProps)) {
			String res = "";
			// 1. Split list of properties by whitespace: -Dfoo.bar=5 -Dfrob=2
			final String[] props = sysProps.split(" ");
			for (int i = 0; i < props.length; i++) {
				// 2. Split each property by equal sign
				final String[] prop = props[i].split("=");
				// 3. skip any prop that does not consist out of 2 elements (key & value)
				if (prop.length == 2) {
					String key = prop[0];
					// 4. Strip off -D parameter if given
					if (key.startsWith("-D")) {
						key = key.substring(2, key.length());
					}
					final String value = prop[1];
					res += "<property name=\"" + key + "\" value=\"" + value + "\"/>\n";
				} else {
					// 5. write hint into res indicating which property is broken
					res += "<!-- Broken system property (key or value missing) " + props[i] + " -->\n";
				}
			}
			return res;
		} else {
			return "";
		}
	}

	/**
	 * Reads the "vmargs" query part from the remote request which can be used
	 * to pass VM args to the forked java process. E.g.
	 * 
	 * <pre>
	 * <code>http://localhost:10996/worker.jnlp?vmargs=-Xmx1024m%20-XX:MaxDirectMemorySize=512m</code>
	 * </pre>
	 * 
	 * results in <code>-Xmx1024 -XX:MaxDirectMemorySize=512m</code> being passed. If no
	 * vmargs are given or vmargs is empty, it returns the empty string <code>""</code>.
	 * <p>
	 * 
	 * @see http://docs.oracle.com/javase/7/docs/technotes/guides/javaws/developersguide/syntax.html for a list of allowed vm arguments
	 * 
	 * @param req
	 *            The {@link HttpServletRequest} representing the user defined
	 *            url with a query part if any.
	 * @return A list of (additional) VM arguments extracted from the
	 *         {@link HttpServletRequest}'s "vmargs" query part. If no vmargs
	 *         query part is given, the empty string is returned.
	 */
	private String getVMArgs(final HttpServletRequest req) {
		final String vmargs = req.getParameter(VM_ARGS);
		if (vmargs != null && !"".equalsIgnoreCase(vmargs)) {
			return "java-vm-args=\"" + vmargs + "\"";
		} else {
			return "";
		}
	}
}