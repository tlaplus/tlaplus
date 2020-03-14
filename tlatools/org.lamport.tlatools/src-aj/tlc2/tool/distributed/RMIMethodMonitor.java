package tlc2.tool.distributed;

import java.util.HashMap;
import java.util.Map;

import org.aspectj.lang.JoinPoint;
import org.aspectj.lang.Signature;

public class RMIMethodMonitor {

	/**
	 * Holder to count invocations per remote method
	 */
	private static final Map<String, Integer> invoctions = new HashMap<String, Integer>();
	
	/**
	 * @param joinPoint Counts the invocation for the given joinPoint
	 */
	public static synchronized void entering(JoinPoint joinPoint) {
		final Signature signature = joinPoint.getSignature();
		final String methodName = signature.toShortString();
		Integer invocedTimes = invoctions.get(methodName);
		
		if(invocedTimes == null) {
			invoctions.put(methodName, 1);
		} else {
			int i = invocedTimes.intValue();
			invoctions.put(methodName, ++i);
		}
	}

	public static synchronized Map<String, Integer> getInvocations() {
		return invoctions;
	}
}
