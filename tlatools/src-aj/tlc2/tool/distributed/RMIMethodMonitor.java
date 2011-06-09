package tlc2.tool.distributed;

import java.util.HashMap;
import java.util.Map;

import org.aspectj.lang.JoinPoint;

public class RMIMethodMonitor {
	
	/**
	 * Holder to count invocations per remote method
	 */
	private static Map<String, Integer> invoctions = new HashMap<String, Integer>();
	
	/**
	 * @param joinPoint Counts the invocation for the given joinPoint
	 */
	public static synchronized void entering(JoinPoint joinPoint) {
		final String methodName = joinPoint.toLongString();
		Integer invocedTimes = invoctions.get(methodName);
		
		if(invocedTimes == null) {
			invoctions.put(methodName, 1);
		} else {
			invoctions.put(methodName, invocedTimes++);
		}
	}

	public static Map<String, Integer> getInvocations() {
		return invoctions;
	}
}
