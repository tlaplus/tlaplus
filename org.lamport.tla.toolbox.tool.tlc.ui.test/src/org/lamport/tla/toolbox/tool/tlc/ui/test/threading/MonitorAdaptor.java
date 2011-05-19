package org.lamport.tla.toolbox.tool.tlc.ui.test.threading;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.aspectj.lang.JoinPoint;
import org.eclipse.swtbot.swt.finder.utils.SWTUtils;

public class MonitorAdaptor {

	/**
	 * Set of all triggered join points
	 */
	private static Set<JoinPoint> joinPoints = new HashSet<JoinPoint>();

	/**
	 * Checks if the current joinPoint has been triggered inside the main (UI)
	 * thread
	 * 
	 * @param joinPoint
	 */
	public static void enter(JoinPoint joinPoint) {
		final Thread currentThread = Thread.currentThread();
		final Thread swtThread = SWTUtils.display().getThread();
		if (currentThread == swtThread) {
			joinPoints.add(joinPoint);
//				System.err.println("Called backend code from UI thread!!! "
//						+ joinPoint.toLongString());
		}
	}

	public static boolean hasTriggeredBackendCode() {
		return !joinPoints.isEmpty();
	}

	public static Set<JoinPoint> getTriggeredJoinPoints() {
		return Collections.unmodifiableSet(joinPoints);
	}

	public static void reset() {
		joinPoints.clear();
	}

	/**
	 * Holder for the aspect
	 */
	private static Object aspect;
	
	public static void setAspect(Object o) {
		aspect = o;
	}
	
	public static boolean aspectIsActive() {
		return aspect != null;
	}
}
