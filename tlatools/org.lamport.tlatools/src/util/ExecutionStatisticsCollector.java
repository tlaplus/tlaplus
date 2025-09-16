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
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.net.HttpURLConnection;
import java.net.InetAddress;
import java.net.NetworkInterface;
import java.net.SocketException;
import java.net.URL;
import java.net.URLEncoder;
import java.nio.file.NoSuchFileException;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Map;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;

public class ExecutionStatisticsCollector {

	static final String RND_ID_STR = "RANDOM_IDENTIFIER";
	static final String NO_ESC_STR = "NO_STATISTICS";
	
	public enum Selection {
		ON, RANDOM_IDENTIFIER, NO_ESC;

		@Override
		public String toString() {
			if (this == ON) {
				return getRandomIdentifier();
			} else if (this == RANDOM_IDENTIFIER) {
				return RND_ID_STR;
			} else {
				return NO_ESC_STR;
			}
		}
	}
	
	private static final String PATH = System.getProperty("user.home", "") + File.separator + ".tlaplus" + File.separator + "esc.txt";
	
	private static final String HOSTNAME = System.getProperty(ExecutionStatisticsCollector.class.getName() + ".domain", "tlaplus-execution-stats-collection01");

	public static final String PROP = ExecutionStatisticsCollector.class.getName() + ".id";
	
	private final String pathname;
	private final String hostname;

	public ExecutionStatisticsCollector() {
		this(PATH, HOSTNAME);
	}
	ExecutionStatisticsCollector(String path) {
		this.pathname = path;
		this.hostname = HOSTNAME;
	}
	
	ExecutionStatisticsCollector(String path, final String hostname) {
		this.pathname = path;
		this.hostname = hostname;
	}
	
	public void collect(final Map<String, String> parameters) {
		// Execution statistics reporting is designed to be minimally invasive and
		// should not interfere with model checking. However, if model checking
		// completes immediately, there may not be enough time for the execution
		// statistics to be properly reported. Additionally, the recently added DNS
		// lookup step has increased the time required for reporting, making delays more
		// likely. To address this, a new Java system property
		// (`-Dutil.ExecutionStatisticsCollector.waitForCompletion=true`) has been
		// introduced. When enabled, this property forces TLC to wait until execution
		// statistics have been fully reported, i.e., until the URL connection has
		// completed. This behavior only applies if execution statistics reporting is
		// enabled.
		collectAsync(parameters, Boolean.getBoolean(ExecutionStatisticsCollector.class.getName() + ".waitForCompletion"));
	}

	protected void collectAsync(final Map<String, String> parameters, final boolean waitForCompletion) {
		// Do not block TLC startup but send this to the background immediately. If
		// dontWaitForCompletion is true, the VM will terminate this thread regardless
		// of its state if the VM decides to shutdown (e.g. because TLC is done).
		final CompletableFuture<Void> collector = CompletableFuture.runAsync(() -> {
			collect0(parameters);
		});

		if (waitForCompletion) {
			// The JVM does not wait for non-daemon threads to finish before terminating
			// when termination is triggered by System.exit. TLC calls System.exit in
			// several places. Thus, we add a shutdown hook that waits for the thread to
			// finish.
			Runtime.getRuntime().addShutdownHook(new Thread(() -> {
				try {
					collector.get(10, TimeUnit.SECONDS);
				} catch (Exception ignored) {
				}
			}, "TLC Execution Statistics Collector Shutdown Hook"));
		}
	}
	
	protected void collect0(final Map<String, String> parameters) {
		/*
		 * | `esc.txt`               | DNS Query | DNS Query Succeeds (Private Reporting) | DNS Query NXDOMAIN (Public Reporting) |
		 * |-------------------------|-----------|----------------------------------------|---------------------------------------|
		 * | `NO_STATISTICS`         | n         | N/A                                    | N/A                                   |
		 * | Unreadable `esc.txt`    | n         | N/A                                    | N/A                                   |
		 * | No `esc.txt` or empty   | y         | UUIDv1                                 | N/A                                   |
		 * | `RANDOM_IDENTIFIER`     | y         | UUIDv4                                 | UUIDv4                                |
		 * | Some string `S`         | y         | `S`                                    | `S`                                   |
		 * |-------------------------|-----------|----------------------------------------|---------------------------------------|
		 */
		String line = null;

		// Check if the installation explicitly requested opt-out by having created the
		// file containing the NO_ESC_STR.
		final File udcFile = new File(pathname);
		if (udcFile.exists()) {
			try (BufferedReader br = new BufferedReader(new FileReader(udcFile))) {
				line = br.readLine();
				if (line != null && NO_ESC_STR.equals(line.trim())) {
					return;
				}
			} catch (FileNotFoundException | NoSuchFileException swallow) {
			    // file does not exist; continue because the user has not expressed a preference.
			} catch (IOException diableExecStatsSilently) {
			    return;
			}
		}
        
		// The installation has not opted out. Check whether the installation's
		// corporate owner (if any) wants to receive execution statistics.
		// See: https://github.com/tlaplus/tlaplus/issues/1170
		final InetAddress optIn = getOptInDNSRecord();
        
		if (optIn == null) {
			final String id = getIdentifier(line);
			if (id != null) {
				// Include identifier to track individual installations (not users!).
				parameters.put("id", id);
				submit("esc01.tlapl.us", parameters);
			}
		} else {
			// We use `getCanonicalHostName` instead of `getHostName` to resolve
			// 'tlaplus-execution-stats-collection01' to its fully qualified domain name
			// (FQDN), 'tlaplus-execution-stats-collection01.frob.com'. If we used
			// `getHostName`, the TLS handshake during submission would fail because no
			// valid TLS certificate includes a Subject Alternative Name (SAN) matching
			// 'tlaplus-execution-stats-collection01.*'. (Issuing a certificate like that
			// would effectively allow hijacking of HTTPS requests across any domain.)
			//
			// However, it's important to note that `getCanonicalHostName` performs a
			// *reverse DNS lookup*. That means the hostname
			// 'tlaplus-execution-stats-collection01' is first resolved to an IP address,
			// which is then reverse-resolved to a domain name. If this reverse lookup does
			// *not* resolve to `'tlaplus-execution-stats-collection01.frob.com'`, the TLS
			// handshake will still fail.
			final String chn = optIn.getCanonicalHostName();
			if (line == null || line.trim().isEmpty()) {
				parameters.put("id", getUUIDv1());
				submit(chn, parameters);
				return;
			}
			final String id = getIdentifier(line);
			if (id != null) {
				parameters.put("id", id);
				submit(chn, parameters);
				return;
			}
		}
	}

	private InetAddress getOptInDNSRecord() {
		InetAddress optIn = null;
		try {
			optIn = InetAddress.getByName(hostname);
		} catch (Exception swallow) {
		}
		return optIn;
	}

	public String getIdentifier(String identifier) {
		if (System.getProperty(PROP) != null) {
			return System.getProperty(PROP);
		}

		if (identifier == null || NO_ESC_STR.equals(identifier.trim())) {
			// File is empty or its first line is "NO_STATISTICS".
			return null;
		} else if (RND_ID_STR.equals(identifier.trim())) {
			identifier = getRandomIdentifier();
		}
		
		// truncate the identifier no matter what, but first remove leading and trailing whitespaces.
		final String trimmed = identifier.trim();
		return trimmed.substring(0, Math.min(trimmed.length(), 32));
	}

	public String getIdentifier() {
		if (System.getProperty(PROP) != null) {
			return System.getProperty(PROP);
		}
		String identifier;

		final File udcFile = new File(pathname);
		if (!udcFile.exists()) {
			// No file ~/.tlaplus/esc.txt.
			return null;
		}
		try (BufferedReader br = new BufferedReader(new FileReader(udcFile))) {
			identifier = br.readLine();
		} catch (Exception e) {
			// Something went wrong reading file ~/.tlaplus/esc.txt
			return null;
		}
		return getIdentifier(identifier);
	}

	private boolean escFileExists() {
		return new File(pathname).exists();
	}

	public boolean isEnabled() {
		// The getOptINDNSRecord function may block execution because of network I/O. As
		// a result, any code that calls isEnabled in the Toolbox may also be blocked.
		// Two of the known callers are Jobs that are built to handle blocking
		// operations. However, the opt-in/out dialog in the Toolbox UI also invokes
		// isEnabled. In that specific case, it was considered acceptable for the UI
		// thread to potentially be blocked. If isEnabled doesn't take getOptInDNSRecord
		// into account, a user cannot explicitly opt-out of company-level execution
		// statistics because the dialog's opt-out button is only clickable if 
		// execution statistics are currently enabled.
		return getIdentifier() != null || getOptInDNSRecord() != null;
	}

	public void set(final Selection c) throws IOException {
		final File udcFile = new File(PATH);
		// Create ~/.tlaplus/ parent directory if it doesn't exist. This will probably
		// only ever be the case on a development machine where the Toolbox runs from
		// inside Eclipse with a workspace location ("-data") other than ~/.tlaplus/ .
		udcFile.getParentFile().mkdirs();
		udcFile.createNewFile();
		
		try (BufferedWriter br = new BufferedWriter(new FileWriter(udcFile))) {
			br.write(c.toString() + "\n");
		} catch (IOException e) {
			throw e;
		}
	}
	
	public Selection get() {
		if (isEnabled()) {
			try (BufferedReader br = new BufferedReader(new FileReader(new File(pathname)))) {
				String line = br.readLine();
				if (RND_ID_STR.equals(line)) {
					return Selection.RANDOM_IDENTIFIER;
				} else {
					return Selection.ON;
				}
			} catch (Exception e) {
			}
		}
		return Selection.NO_ESC;
	}
	
	public static boolean promptUser() {
		return !(new ExecutionStatisticsCollector().escFileExists());
	}

	private static String getRandomIdentifier() {
		return UUID.randomUUID().toString().replaceAll("-", "");
	}

	// Send the request.
	protected void submit(final String hostname, final Map<String, String> parameters) {
		// Include a timestamp to cause HEAD to be un-cachable.
		parameters.put("ts", Long.toString(System.currentTimeMillis()));
		parameters.put("optout", Boolean.FALSE.toString());
		
		try {
			final URL url = new URL((Boolean.getBoolean(ExecutionStatisticsCollector.class.getName() + ".nossl") ? "http"
					: "https") + "://" + hostname + "/?" + encode(parameters));

			final HttpURLConnection con = (HttpURLConnection) url.openConnection();
			con.setRequestMethod("HEAD");
			con.getResponseMessage();
			con.disconnect();
		} catch (Exception ignoreCompletely) {
			// A TLC user doesn't care if execution statistics collection doesn't work.
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
	
	private static byte[] getMacAddress() {
		try {
			final Enumeration<NetworkInterface> ifaces = NetworkInterface.getNetworkInterfaces();

			while (ifaces.hasMoreElements()) {
				final NetworkInterface iface = ifaces.nextElement();
				// An interface may not have an address, or a security manager may prevent
				// access to it.
				try {
					final byte[] hardwareAddress = iface.getHardwareAddress();
					if (hardwareAddress != null) {
						return hardwareAddress;
					}
				} catch (final SocketException swallow) {
				}
			}
		} catch (final SocketException swallow) {
		}
		return null;
	}
	
	private String getUUIDv1() {
		final byte[] mac = getMacAddress();
		if (mac == null) {
			return getRandomIdentifier();
		}

		final long uuidEpochOffset = -12219292800000L;
		final long millisSinceUuidEpoch = System.currentTimeMillis() - uuidEpochOffset;
		final long timestamp = millisSinceUuidEpoch * 10_000;

		final long timeLow = timestamp & 0xFFFFFFFFL;
		final long timeMid = (timestamp >>> 32) & 0xFFFFL;
		long timeHi = (timestamp >>> 48) & 0x0FFFL;
		timeHi |= 0x1000;

		final long mostSigBits = (timeLow << 32) | (timeMid << 16) | timeHi;

		long clockSeq = (long) (Math.random() * 0x3FFF);
		clockSeq |= 0x8000;

		final long leastSigBits = (clockSeq << 48) | ((mac[0] & 0xFFL) << 40) | ((mac[1] & 0xFFL) << 32)
				| ((mac[2] & 0xFFL) << 24) | ((mac[3] & 0xFFL) << 16) | ((mac[4] & 0xFFL) << 8) | (mac[5] & 0xFFL);

		return new UUID(mostSigBits, leastSigBits).toString().replaceAll("-", "");
	}

	// for manual testing //
	
	public static void main(String[] args) {
		new ExecutionStatisticsCollector().collect0(new HashMap<>());
	}
}
