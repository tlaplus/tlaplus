package tlc2.tool.distributed;

import java.util.Date;

public aspect TLCServerMonitorAspect {
	
	private Date processStartTime, computationStartTime;
	private TLCServer server;
	
	// catch main method call in TLCServer
	pointcut callToMainMethod() : 
		   execution(* tlc2.tool.distributed.TLCServer.main(..));
	
	before() : (callToMainMethod()) {
		processStartTime = new Date();
	}
	
	after() : (callToMainMethod()) {
		TLCStatistics.writeStats(server, processStartTime, computationStartTime, new Date());
	}
	
	// catch modelCheck method call in TLCServer
	pointcut callToModelCheckMethod(TLCServer aServer) : 
		call(void tlc2.tool.distributed.TLCServer.modelCheck(TLCServer)) && args(aServer);
	
	before(TLCServer aServer) : (callToModelCheckMethod(aServer)) {
		computationStartTime = new Date();
		server = aServer;
	}
}
