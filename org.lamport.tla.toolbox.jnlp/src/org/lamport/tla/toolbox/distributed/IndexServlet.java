// Copyright (c) 2011 Microsoft Corporation. All rights reserved.
package org.lamport.tla.toolbox.distributed;

import java.io.IOException;
import java.io.PrintWriter;

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

		final PrintWriter writer = resp.getWriter();
		writer.println("<!DOCTYPE html>");

		writer.println(
				"<html><head>\n" + 
						"<title>Distributed TLC</title>\n" + 
				"</head><body>");
		
		// boostrap JRE on Windows systems
		writer.println(
				"<object codebase=\"http://java.sun.com/update/1.7.0/jinstall-7u80-windows-i586.cab#Version=7,0,0,0\" classid=\"clsid:5852F5ED-8BF4-11D4-A245-0080C6F74284\" height='0' width='0'>" +
						"<param name=\"app\" value=\"" + addr + "\"/>" +
						"<param name=\"back\" value=\"false\"/>" +
				"</object>");
		
		writer.println(
				"<p style=\"margin: 12px 20px;\">" +
				"<b>Please note:</b> " +
				"Starting with the 1.6.1 release of the Toolbox, we have removed the JNLP functionality previously " +
				"found on this page. This is due to our move towards full Java 11+ usage (support for Java WebStart " +
				"was removed beginning with Java 9.)" + 
				"<br/>" +
				"<ul>" + 
				"<li>If you found the JNLP functionality to be critical to your usage, please open an issue at " +
				"<a href=\"https://github.com/tlaplus/tlaplus/issues\" target=_blank>our GitHub repository.</a></li>" +
				"<li>If you would like to take over development and deployment support for the JNLP related " +
				"functionality, please contact us.</li>" +
				"</ul>" + 
				"</p>" +
				"<hr style=\"margin-left: auto; margin-right: auto; width: 67%\"/>");
		
		// TLC worker
		printTable(writer, JNLPGeneratorServlet.JNLP, JNLPGeneratorServlet.MAINCLASS, "worker",
				JNLPGeneratorServlet.INDEX_DESC);

		// Fingerprint server
		printTable(writer, FPSetJNLPGeneratorServlet.JNLP, FPSetJNLPGeneratorServlet.MAINCLASS, "fingerprint set",
				FPSetJNLPGeneratorServlet.INDEX_DESC);
		
		// Combined fingerprint server and TLC worker
		printTable(writer, CombinedJNLPGeneratorServlet.JNLP, CombinedJNLPGeneratorServlet.MAINCLASS, "combined",
				CombinedJNLPGeneratorServlet.INDEX_DESC);
		
		// d) dist-tlc.zip OSGi fw that acts as a TLCWorker daemon
		writer.println(
				"<table id=\"header\" cellpadding=\"0\" cellspacing=\"0\" width=\"100%\" border=\"0\">\n" + 
					"<p style=\"font-size: 125%; font-weight: 700;\">Start a daemon-stlye TLCWorker (no need " +
						"to restart the worker for each model checker run)</p>\n" + 
					"<tr><td>\n" + 
					"<ul>");
			
		writer.println(
				"<li>\n" + 
					"<p>Run from slave command line (works best with <a href=\"http://www.oracle.com/technetwork/java/javase/downloads/index.html\">Java 8</a>):</p>\n" + 
					// Linux
					"<h4>bash</h4>" +
					"<pre>\n" + 
						"wget <a href=\"" + addr + "/files/dist-tlc.zip\">" + addr + "/files/dist-tlc.zip</a>\n" + 
						"unzip dist-tlc.zip\n" + 
						"cd disttlc/\n" + 
						 "java -Djava.rmi.server.hostname="
														+ remoteAddr
														+ " -Dorg.lamport.tla.distributed.consumer.TLCWorkerConsumer.uri=rmi://"
														+ url.getHost()
														+ ":10997 "
//														+ "-Dorg.lamport.tla.distributed.consumer.DistributedFPSetConsumer.uri=rmi://"
//														+ url.getHost()	+ ":10997 "
														+ "-jar dist-tlc.jar "
														+					"\n</pre>\n" + 
					// Windows Powershell 2.0 with manually created C:\\tmp folder ($env:temp does not seem to work) and x86 Java installed in default location
					"<h4>Windows Powershell 2.0:</h4>" +
					"<pre>\n" + 
						"(new-object System.Net.WebClient).DownloadFile(\"" + addr + "/files/dist-tlc.zip\", \"C:\\tmp\\dist-tlc.zip\")\n" + 
						"(new-object -com shell.application).namespace(\"C:\\tmp\").CopyHere((new-object -com shell.application).namespace(\"C:\\tmp\\dist-tlc.zip\").Items(),16)\n" +
						 "& 'C:\\Program Files (x86)\\Java\\jre7\\bin\\java.exe' \"-Djava.rmi.server.hostname="
														+ remoteAddr
														+ "\" \"-Dorg.lamport.tla.distributed.consumer.TLCWorkerConsumer.uri=rmi://"
														+ url.getHost()
														+ ":10997\" "
//														+ "\"-Dorg.lamport.tla.distributed.consumer.DistributedFPSetConsumer.uri=rmi://"
//														+ url.getHost()	+ ":10997\" "
														+ "-jar C:\\tmp\\disttlc\\dist-tlc.jar"
														+				"\n</pre>\n" + 
				"</li>");
		writer.println(
				"</ul>\n" + 
				"</td></tr></table>\n");
		
		writer.println(
				"</body></html>");
	}

	private void printTable(final PrintWriter writer, final String jnlpName, final String mainClass, final String name, final String description) throws IOException {
		writer.println(
				"<table id=\"header\" cellpadding=\"0\" cellspacing=\"0\" width=\"100%\" border=\"0\">\n" + 
					"<p style=\"font-size: 125%; font-weight: 700;\">" + description + "</p>\n" + 
					"<tr><td>\n");// + 
//					"<ul>");
			
		// a) direct link
//		writer.println(
//				"<li>\n" + 
//						"<p><a href=\"" + jnlpName + "\" id=\"jnlp-link\"><img alt=\"launch FPSet\" src=\"/files/webstart.gif\" /> Launch "
//								+ name + " from browser</a></p>\n" + 
//				"</li>");
		
		// b) command line
//		writer.println(
//				"<li>\n" + 
//					"<p>Run from slave command line:</p>\n" + 
//					"<p><pre>" + 
//						"javaws " + addr + "/" + jnlpName +
//					"</pre></p>\n" + 
//				"</li>");
		
		// c) headless
		writer.println(
//				"<li>\n" + 
//					"<p>Or if the slave is headless:</p>\n" + 
					"<pre>\n" + 
						"wget " + addr + "/files/" + TLA2TOOLS_JAR + "\n" + 
						"java -Djava.rmi.server.hostname=" + remoteAddr
								+ " -cp <a href=\"/files/" + TLA2TOOLS_JAR + "\">" + TLA2TOOLS_JAR + "</a> " + mainClass
						+ " " + url.getHost() + "\n" +
					"</pre>\n"); // + 
//				"</li>");
		
		writer.println(
//				"</ul>\n" + 
				"</td></tr></table>\n" +
				"<hr style=\"margin-left: auto; margin-right: auto; width: 67%\"/>");
	}
}
