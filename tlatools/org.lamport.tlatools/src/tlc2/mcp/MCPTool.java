/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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
 *   Markus Alexander Kuppe - initial implementation
 ******************************************************************************/
package tlc2.mcp;

import java.io.File;
import java.net.URLClassLoader;
import java.util.Set;

import javax.management.MBeanServer;
import javax.management.ObjectName;

import com.google.gson.JsonObject;

/**
 * Abstract base class for MCP tools.
 * 
 * Each tool implementation provides: - A description of what the tool does - An
 * input schema (JSON Schema) defining expected parameters - An execute method
 * that performs the tool's operation
 * 
 * This class provides common functionality for isolated class loading, MBean
 * cleanup, and classpath handling to ensure proper static state isolation
 * between runs.
 */
public abstract class MCPTool {

	/**
	 * Interface for sending notifications to the MCP client during tool execution.
	 */
	public interface NotificationSender {
		/**
		 * Send a notification message to the client.
		 * 
		 * @param message The notification message to send
		 */
		void sendNotification(String message);
	}

	/**
	 * Isolated class loader that reloads all TLC-related classes to ensure static
	 * state isolation between runs. Based on
	 * DumpLoadTraceTest.DumpLoadIsolatedClassLoader.
	 */
	protected static class IsolatedClassLoader extends URLClassLoader {

		private final java.util.Map<String, Class<?>> cache = new java.util.HashMap<>();
		private final java.util.Set<String> packages = new java.util.HashSet<>();

		public IsolatedClassLoader(java.net.URL[] urls, ClassLoader parent) {
			super(urls, parent);

			// All of TLC's java packages that need isolation
			packages.add("tla2sany");
			packages.add("pcal");
			packages.add("util");
			packages.add("tla2tex");
			packages.add("tlc2");
		}

		@Override
		public Class<?> loadClass(String name) throws ClassNotFoundException {
			// Check if we've already loaded this class in this loader instance
			synchronized (getClassLoadingLock(name)) {
				Class<?> c = findLoadedClass(name);
				if (c != null) {
					return c;
				}

				// Check cache
				if (cache.containsKey(name)) {
					return cache.get(name);
				}

				// For classes in our isolated packages, load them ourselves
				for (final String pkg : packages) {
					if (name.startsWith(pkg)) {
						try {
							c = findClass(name);
							cache.put(name, c);
							return c;
						} catch (LinkageError e) {
							// If we get a LinkageError, the class might already be loaded by parent
							// Fall back to parent delegation
							break;
						}
					}
				}

				// Delegate to parent for all other classes
				return super.loadClass(name);
			}
		}
	}

	/**
	 * Extract URLs from the classpath for creating an isolated class loader. Needed
	 * for Java 9+ where the system class loader is not a URLClassLoader.
	 * 
	 * @return Array of URLs from the classpath
	 * @throws Exception if classpath parsing fails
	 */
	protected java.net.URL[] getClasspathURLs() throws Exception {
		final String classpath = System.getProperty("java.class.path");
		final String[] entries = classpath.split(File.pathSeparator);
		final java.net.URL[] urls = new java.net.URL[entries.length];
		for (int i = 0; i < entries.length; i++) {
			urls[i] = new File(entries[i]).toURI().toURL();
		}
		return urls;
	}

	/**
	 * Create an isolated class loader for TLC/SANY execution.
	 * 
	 * @return IsolatedClassLoader instance
	 * @throws Exception if class loader creation fails
	 */
	protected IsolatedClassLoader createIsolatedClassLoader() throws Exception {
		ClassLoader currentLoader = getClass().getClassLoader();

		// Extract URLs for the isolated class loader
		java.net.URL[] urls;
		if (currentLoader instanceof URLClassLoader) {
			// If we have a URLClassLoader, use its URLs
			urls = ((URLClassLoader) currentLoader).getURLs();
		} else {
			// Java 9+: Extract URLs from classpath
			urls = getClasspathURLs();
		}

		return new IsolatedClassLoader(urls, currentLoader.getParent());
	}

	/**
	 * Unregister all TLC-related MBeans from the platform MBeanServer.
	 * 
	 * <p>
	 * <b>Why this is necessary:</b>
	 * </p>
	 * 
	 * <p>
	 * TLC/SANY may register MBeans in the <b>JVM-global platform MBeanServer</b>,
	 * which is a singleton shared across all class loaders. These MBeans persist
	 * even after the isolated class loader is closed. This method cleans up all TLC
	 * MBeans after execution to prevent registration conflicts in subsequent runs.
	 * </p>
	 */
	protected void unregisterTLCMBeans() {
		try {
			MBeanServer mbs = java.lang.management.ManagementFactory.getPlatformMBeanServer();

			// Find all TLC-related MBeans (they start with "tlc2.")
			Set<ObjectName> mbeans = mbs.queryNames(new ObjectName("tlc2.*:*"), null);

			for (ObjectName name : mbeans) {
				try {
					mbs.unregisterMBean(name);
				} catch (Exception e) {
					// Ignore errors during cleanup
					System.err.println("Warning: Could not unregister MBean: " + name + " - " + e.getMessage());
				}
			}
		} catch (Exception e) {
			// Ignore errors during cleanup
			System.err.println("Warning: Error during MBean cleanup: " + e.getMessage());
		}
	}

	/**
	 * Get the human-readable description of this tool.
	 * 
	 * @return Tool description
	 */
	public abstract String getDescription();

	/**
	 * Get the JSON Schema for this tool's input parameters.
	 * 
	 * @return JSON Schema object describing the input parameters
	 */
	public abstract JsonObject getInputSchema();

	/**
	 * Execute the tool with the given arguments.
	 * 
	 * This is the base method that simple tools should override. Tools that don't
	 * need notification support can override only this method.
	 * 
	 * @param arguments JSON object containing the tool's input parameters
	 * @return JSON object containing the tool's result
	 * @throws Exception if tool execution fails
	 */
	public JsonObject execute(JsonObject arguments) throws Exception {
		// This should be overridden by subclasses that don't need notifications
		throw new UnsupportedOperationException(
				"Tool must implement either execute(JsonObject) or execute(JsonObject, NotificationSender)");
	}

	/**
	 * Execute the tool with the given arguments and a notification sender.
	 * 
	 * This method allows tools to send progress notifications during execution.
	 * Tools that want to stream progress updates should override this method.
	 * By default, this delegates to the single-parameter version for backwards
	 * compatibility with tools that only override execute(JsonObject).
	 * 
	 * @param arguments          JSON object containing the tool's input parameters
	 * @param notificationSender Callback for sending progress notifications (may be
	 *                           null)
	 * @return JSON object containing the tool's result
	 * @throws Exception if tool execution fails
	 */
	public JsonObject execute(JsonObject arguments, NotificationSender notificationSender) throws Exception {
		// Default implementation: call the single-parameter version (for backwards compatibility)
		return execute(arguments);
	}
}
