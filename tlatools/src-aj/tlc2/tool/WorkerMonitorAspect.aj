package tlc2.tool;


public aspect WorkerMonitorAspect perthis(callToRunMethod()) {
	
	private long threadStartTime, threadEndTime;
	
	pointcut callToRunMethod() : 
		   execution(* tlc2.tool.Worker.run(..));
	
	before(): (callToRunMethod()) {
		threadStartTime = System.currentTimeMillis();
	}

	after(): (callToRunMethod()) {
		threadEndTime = System.currentTimeMillis();
		WorkerMonitor.addPerformanceResult((Worker) thisJoinPoint.getTarget(), (threadEndTime - threadStartTime));
	}
//	
//	pointcut callToSetUpMethod() :
//		execution(* tlc2.tool.liveness.MultiThreadedSpecTest.setUp());
//	
//	before(): (callToSetUpMethod()) {
//		Object target = thisJoinPoint.getTarget();
//		System.out.println("SetUp pc: " + target);
//	}
}
