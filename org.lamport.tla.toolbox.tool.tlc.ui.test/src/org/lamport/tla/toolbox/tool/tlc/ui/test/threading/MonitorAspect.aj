package org.lamport.tla.toolbox.tool.tlc.ui.test.threading;

/**
 * The purpose of this advice is to intercept method execution in the backend
 * code - namely all code in the packages tlc2, tla2sany, tla2tex, pcal and util.
 * 
 * It notifies the {@link MonitorAdaptor} about the method execution.
 */
public aspect MonitorAspect {

	before(): (execution(* tlc2..*.*(..))
			|| execution(* tla2sany..*.*(..))
			|| execution(* tla2tex..*.*(..))
			|| execution(* pcal..*.*(..))
			|| execution(* util..*.*(..)))
		&& !within(org.lamport.tla.toolbox.tool.tlc.ui.test..*) {
		MonitorAdaptor.enter(thisJoinPoint);
	}
}
