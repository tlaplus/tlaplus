package org.lamport.tla.toolbox.test.threading;

import org.aspectj.lang.annotation.SuppressAjWarnings;

/**
 * The purpose of this advice is to intercept method execution in the backend
 * code - namely all code in the packages tlc2, tla2sany, tla2tex, pcal and util.
 * 
 * It notifies the {@link MonitorAdaptor} about the method execution.
 */
public aspect MonitorAspect {

	public MonitorAspect() {
		MonitorAdaptor.setAspect(this);
	}
	
	// known places where backend call within UI thread are acceptable
	pointcut inFilter() : 
		withincode(public boolean org.lamport.tla.toolbox.util.ResourceHelper.isValidSpecName(String));

	// catch all method calls (static and object ones)
	pointcut callToBackend() : 
		   execution(* tlc2..*.*(..))
		|| execution(* tla2sany..*.*(..))
		|| execution(* tla2tex..*.*(..))
		|| execution(* pcal..*.*(..))
		|| execution(* util..*.*(..));
	
	// capture calls to backend, but not within ourself or in filter
	before(): (callToBackend()
			&& !cflowbelow(callToBackend()) && !cflowbelow(inFilter())) { 
		MonitorAdaptor.enter(thisJoinPoint);
	}
}
