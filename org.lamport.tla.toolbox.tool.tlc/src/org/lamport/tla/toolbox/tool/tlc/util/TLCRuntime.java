// Copyright (c) Dec 26, 2011 Microsoft Corporation.  All rights reserved.

package org.lamport.tla.toolbox.tool.tlc.util;

import java.lang.management.ManagementFactory;
import java.lang.management.OperatingSystemMXBean;
import java.lang.reflect.Method;

/**
 * @author Markus Alexander Kuppe
 */
public class TLCRuntime {
	
	private static TLCRuntime runtime;
	
	public static TLCRuntime getInstance() {
		if(runtime == null) {
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
	 * @param fraction The percentage of physical memory required
	 * @return the absolute amount of physical memory in MB
	 */
	public long getAbsolutePhysicalSystemMemory(double fraction) {
		if(physicalSystemMemory == -1) {
			physicalSystemMemory = getPhysicalSystemMemory();
		}
        final double d = physicalSystemMemory * fraction;
        return (long) (d / 1024d / 1024d);
	}
}
