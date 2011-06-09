package tlc2.tool.distributed;

public aspect RMIMethodMonitorAspect {

	// catch all method calls to RMI methods
	pointcut callToRemoteMethod() : 
		   execution(* tlc2.tool.distributed..*.*(..) throws java.rmi.RemoteException);
	
	before(): (callToRemoteMethod()) {
		RMIMethodMonitor.entering(thisJoinPoint);
	}
}
