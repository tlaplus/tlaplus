package org.lamport.tla.toolbox.distributed;

import java.io.IOException;

import javax.servlet.ServletException;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

/**
 * Serves the {@link tlc2.tool.distributed.TLCWorker} jnlp file
 */
public class JNLPGeneratorServlet extends URLHttpServlet {

	private static final String MAIN_CLASS = "tlc2.tool.distributed.TLCWorker";

	private static final long serialVersionUID = 6158685065128002088L;
	
	public static final String SERVLET_NAME = "worker.jnlp";

	/* (non-Javadoc)
	 * @see javax.servlet.http.HttpServlet#doGet(javax.servlet.http.HttpServletRequest, javax.servlet.http.HttpServletResponse)
	 */
	@Override
	protected void doGet(final HttpServletRequest req, final HttpServletResponse resp) throws ServletException, IOException {
		super.doGet(req, resp);
		
		resp.setContentType("application/x-java-jnlp-file");
		
		final String addr = url.getProtocol() + "://" + url.getAuthority();
		
		resp.getWriter().println(
				"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" + 
				"<jnlp codebase=\"" + addr + "\" href=\"" + SERVLET_NAME + "\">\n" +
					"<information>\n" + 
						"<title>" + MAIN_CLASS + "</title>\n" + 
						"<vendor>Microsoft Corp.</vendor>\n" + 
						"<homepage href=\"http://research.microsoft.com/en-us/um/people/lamport/tla/tla.html\"/>\n" + 
						"<description>Distributed TLC worker instance</description>\n" + 
					"</information>\n" + 
					"<security>\n" + 
						"<all-permissions/>\n" + 
					"</security>\n" + 
					"<resources>\n" + 
						"<j2se version=\"1.5+\"/>\n" + 
						"<jar href=\""+ addr + "/files/tla2tools.jar\"/>\n" + 
						//"<property name\"key\" value=\"value\"/>\n" + 
					"</resources>\n" + 
					"<application-desc main-class=\"" + MAIN_CLASS + "\">\n" + 
						"<argument>" + url.getHost() + "</argument>\n" + 
					"</application-desc>\n" + 
				"</jnlp>");
	}
}
        
        
    
    
	
    
    
        
    
    
	
    

