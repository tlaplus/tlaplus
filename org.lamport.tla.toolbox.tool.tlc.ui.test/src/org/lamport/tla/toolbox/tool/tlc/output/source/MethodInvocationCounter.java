package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.LinkedHashMap;
import java.util.Map;

import org.aspectj.lang.JoinPoint;

public class MethodInvocationCounter {
	public static final String TBTOIP_addIncrement = "TagBasedTLCOutputIncrementalParser.addIncrement(..)";
	public static final String TOPCL_documentPartitioningChanged = "TLCOutputPartitionChangeListener.documentPartitioningChanged(..)";

	private static Map<String, Long> invocations = new LinkedHashMap<String, Long>();

	static void enter(JoinPoint joinPoint) {
		String key = joinPoint.getSignature().toShortString();
		Long l = invocations.get(key);
		if(l == null) {
			l = 0L;
		}
		invocations.put(key, ++l);
	}

	/**
	 * @return the invocations
	 */
	public static Map<String, Long> getInvocations() {
		return invocations;
	}
	
	public static void clear() {
		invocations.clear();
	}
}
