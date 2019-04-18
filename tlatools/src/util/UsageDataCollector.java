/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.UnsupportedEncodingException;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.URLEncoder;
import java.util.HashMap;
import java.util.Map;
import java.util.UUID;

public class UsageDataCollector {

	public static final String PROP = UsageDataCollector.class.getName() + ".id";
	
	private final boolean isOptOut;
	private final String pathname;

	public UsageDataCollector() {
		this(isOptOut(), System.getProperty("user.home", "") + File.separator + ".tlaplus" + File.separator + "udc.txt");
	}
	
	UsageDataCollector(String path) {
		this(false, path);
	}
	
	UsageDataCollector(final boolean optOut, final String path) {
		this.isOptOut = optOut;
		this.pathname = path;
	}
	
	public void collect(final Map<String, String> parameters) {
		collect(parameters, true);
	}

	private void collect(final Map<String, String> parameters, final boolean dontWaitForCompletion) {
		// Do not block TLC startup but send this to the background immediately. If
		// dontWaitForCompletion is true, the VM will terminate this thread regardless
		// of its state if the VM decides to shutdown (e.g. because TLC is done).
		final Thread thread = new Thread(new Runnable() {
			@Override
			public void run() {
				if (isEnabled()) {
					// Include identifier to track individual installations (not users!).
					parameters.put("id", getIdentifier());
					submit(parameters, dontWaitForCompletion);
				}
			}
		}, "TLC Usage Data Collector");
		thread.setDaemon(dontWaitForCompletion);
		thread.start();
	}
	
	/*
	 * file == ~/.tlaplus/udc.txt
	 * fl == first line of file interpreted as a string without terminal chars
	 * in/out == opt-in & opt-out
	 * y/r/n == data collected with constant id/data collected with random id/data not collected
	 * 
	 *       | No file | fl unreadable | fl empty | fl = "NO_UDC" | fl = "RANDOM_IDENTIFIER" | fl any other string
	 * ==========================================================================================================
	 * | out |   y     |       n       |    n     |       n       |            r             |         y         |
	 * ----------------------------------------------------------------------------------------------------------
	 * | in  |   n     |       n       |    n     |       n       |            r             |         y         |
	 * ----------------------------------------------------------------------------------------------------------
	 */
	public String getIdentifier() {
		if (System.getProperty(PROP) != null) {
			return System.getProperty(PROP);
		}
		String identifier;

		final File udcFile = new File(pathname);
		if (!udcFile.exists() && isOptOut) {
			try (BufferedWriter br = new BufferedWriter(new FileWriter(udcFile))) {
				br.write(getRandomIdentifier());
			} catch (Exception e) {
				// Something went wrong writing to file ~/.tlaplus/udc.txt. Consider UDC failed.
				return null;
			}
		}
		if (!udcFile.exists()) {
			// No file ~/.tlaplus/udc.txt.
			return null;
		}
		try (BufferedReader br = new BufferedReader(new FileReader(udcFile))) {
			identifier = br.readLine();
		} catch (Exception e) {
			// Something went wrong reading file ~/.tlaplus/udc.txt
			return null;
		}
		if (identifier == null || "NO_UDC".equals(identifier.trim())) {
			// File is empty or its first line is "NO_UDC".
			return null;
		} else if (identifier == null || "RANDOM_IDENTIFIER".equals(identifier.trim())) {
			identifier = getRandomIdentifier();
		}
		
		// truncate the identifier no matter what, but first remove leading and trailing whitespaces.
		return identifier.trim().substring(0, 32);
	}

	public boolean isEnabled() {
		return getIdentifier() != null;
	}
	
	private static String getRandomIdentifier() {
		return UUID.randomUUID().toString().replaceAll("-", "");
	}

	private static boolean isOptOut() {
		return false; // Nobody is opt-out right now
		
		// Below is a way how we could detect Microsoft corpnet machines: This check is
		// conservative because we don't identify Microsoft employees but corporate
		// Microsoft computers.
//		final String userDNSDomain = System.getenv("USERDNSDOMAIN");
//		return userDNSDomain != null && userDNSDomain.toUpperCase().endsWith(".CORP.MICROSOFT.COM");
	}

	// Send the request.
	private static void submit(final Map<String, String> parameters, final boolean dontWaitForCompletion) {
		// Include a timestamp to cause HEAD to be un-cachable.
		parameters.put("ts", Long.toString(System.currentTimeMillis()));
		parameters.put("optout", Boolean.toString(isOptOut()));
		
		try {
			// Opt-out data doesn't report to the opt-in endpoint. The opt-in endpoint is
			// public data, the opt-out endpoint doesn't get shared with the public.
			final URL url = new URL(
					"https://" + (isOptOut() ? "udc02" : "udc01") + ".tlapl.us/?" + encode(parameters));

			final HttpURLConnection con = (HttpURLConnection) url.openConnection();
			con.setRequestMethod("HEAD");
			con.getResponseMessage();
			con.disconnect();
		} catch (Exception ignoreCompletely) {
			// A TLC user doesn't care if usage data collection doesn't work.
		}
	}	
	
	private static String encode(final Map<String, String> parameters) throws UnsupportedEncodingException {
		final StringBuffer buf = new StringBuffer();

		for (String key : parameters.keySet()) {
			String value = parameters.get(key);
			buf.append(URLEncoder.encode(key, "UTF-8"));
			buf.append("=");
			buf.append(URLEncoder.encode(value, "UTF-8"));
			buf.append(",");
		}
		
		return buf.toString().replaceFirst(",$", "");
	}

	// for manual testing //
	
	public static void main(String[] args) {
		new UsageDataCollector().collect(new HashMap<>(), false);
	}
}
