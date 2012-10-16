// Copyright (c) Dec 26, 2011 Microsoft Corporation.  All rights reserved.

package util;

import java.lang.management.ManagementFactory;
import java.lang.management.OperatingSystemMXBean;
import java.lang.management.RuntimeMXBean;
import java.lang.reflect.Method;
import java.util.List;

import tlc2.tool.fp.FPSet;

/**
 * @author Markus Alexander Kuppe
 */
public class TLCRuntime {
	/**
	 * Absolute lower hard limit for {@link FPSet} memory
	 */
	public static final long MinFpMemSize = 20 * (1 << 19);

	private static TLCRuntime runtime;

	/**
	 * @return a {@link TLCRuntime} instance
	 */
	public synchronized static TLCRuntime getInstance() {
		if (runtime == null) {
			runtime = new TLCRuntime();
		}
		return runtime;
	}

	private long physicalSystemMemory = -1;

	/**
	 * @return the total amount of memory, measured in bytes.
	 */
	private long getPhysicalSystemMemory() {

		// try to read the total physical memory via a MXBean. Unfortunately,
		// these methods are not meant as public API, which requires us to pull
		// a visibility reflection hack.
		// This hack is expected to work on Linux, Windows (up to 7) and Max OSX
		final OperatingSystemMXBean operatingSystemMXBean = ManagementFactory
				.getOperatingSystemMXBean();
		for (Method method : operatingSystemMXBean.getClass()
				.getDeclaredMethods()) {
			if (method.getName().equals("getTotalPhysicalMemorySize")) {
				method.setAccessible(true);
				try {
					return (Long) method.invoke(operatingSystemMXBean);
				} catch (Exception e) {
					break;
				}
			}
		}
		// as a safeguard default to the total memory available to this JVM
		return Runtime.getRuntime().totalMemory();
	}

	/**
	 * @param fraction
	 *            The percentage of physical memory required
	 * @return the absolute amount of physical memory in MB
	 */
	public long getAbsolutePhysicalSystemMemory(double fraction) {
		if (physicalSystemMemory == -1) {
			physicalSystemMemory = getPhysicalSystemMemory();
		}
		final double d = physicalSystemMemory * fraction;
		return (long) (d / 1024d / 1024d);
	}
	
	/**
	 * @return The non-heap memory JVM memory set with -XX:MaxDirectMemorySize in Bytes
	 */
	public long getNonHeapPhysicalMemory() {
		// 64MB by default. This happens to be the JVM default for
		// XX:MaxDirectMemorySize if no other value is given.
		long l = (64L * 1024L * 1024L);
		
		final RuntimeMXBean RuntimemxBean = ManagementFactory.getRuntimeMXBean();
		final List<String> arguments = RuntimemxBean.getInputArguments();
		for (String arg : arguments) {
			if (arg.toLowerCase().startsWith("-xx:maxdirectmemorysize")) {
				String[] strings = arg.split("=");
				String mem = strings[1].toLowerCase();
				if (mem.endsWith("g")) {
					l = Long.parseLong(mem.substring(0, mem.length() -1));
					l = l << 30;
					break;
				} else if (mem.endsWith("m")) {
					l = Long.parseLong(mem.substring(0, mem.length() -1));
					l = l << 20;
					break;
				} else if (mem.endsWith("k")) {
					l = Long.parseLong(mem.substring(0, mem.length() -1));
					l = l << 10;
					break;
				} else {
					l = Long.parseLong(mem.substring(0, mem.length()));
					break;
				}
			}
		}
		return l;
	}

	/**
	 * @param fpMemSize
	 *            can be used in two ways:
	 *            <ul>
	 *            <li>to set the relative memory to be used for fingerprints
	 *            (being machine independent)</li>
	 *            <li>to set the absolute memory to be used for fingerprints.
	 *            </li>
	 *            </ul>
	 * 	<p>
	 *            In order to set memory relatively, a value in the domain [0.0,
	 *            1.0] is interpreted as a fraction. A value in the [2,
	 *            Double.MaxValue] domain allocates memory absolutely.
	 * </p>
	 *            Independently of relative or absolute mem allocation, a user
	 *            cannot allocate more than JVM heap space available. Conversely
	 *            there is the lower hard limit {@link TLCRuntime#MinFpMemSize}.
	 * @return a long value that indicates the absolute amount of fingerprints that can potentially fit into VM heap memory
	 */
	//TODO rename to non-fp specific
	public long getFPMemSize(double fpMemSize) {
		// determine amount of memory to be used for fingerprints
		final long maxMemory = Runtime.getRuntime().maxMemory();
		// -fpmem is given
		if (fpMemSize == -1) {
			// .25 * maxMemory
			fpMemSize = maxMemory >> 2;
		}
		// -fpmemratio is given
		if (0 <= fpMemSize && fpMemSize <= 1) {
			fpMemSize = maxMemory * fpMemSize;
		}
		if (fpMemSize < MinFpMemSize) {
			fpMemSize = MinFpMemSize;
		}
		if (fpMemSize >= maxMemory) {
			// .75*maxMemory
			fpMemSize = maxMemory - (maxMemory >> 2);
		}
		return (long) fpMemSize;
	}
}
