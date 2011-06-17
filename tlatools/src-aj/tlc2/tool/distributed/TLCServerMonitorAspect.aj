package tlc2.tool.distributed;

import java.util.Date;

import util.ToolIO;

public aspect TLCServerMonitorAspect {
	
	private Date processStartTime, computationStartTime, computationEndTime;
	private TLCServer server;
	
	// catch main method call in TLCServer
	pointcut callToMainMethod() : 
		   execution(* tlc2.tool.distributed.TLCServer.main(..));

	before() : (callToMainMethod()) {
		processStartTime = new Date();
	}
	
	after() : (callToMainMethod()) {
		if (server != null && processStartTime != null
				&& computationStartTime != null && computationEndTime != null) {
			TLCStatistics.writeStats(server, processStartTime,
					computationStartTime, computationEndTime, new Date());
		} else {
			ToolIO.err
					.println(new Date()
							+ ": Model checking appears to have failed, skipping statistics!");
		}
	}

	// catch setDone method call in TLCServer
	pointcut callToServerDoneMethod() : 
		execution(* tlc2.tool.distributed.TLCServer.setDone(..));
	
	before() : (callToServerDoneMethod()) {
		// record when the _last_ thread finishes!
		computationEndTime = new Date();
	}
	
	// catch modelCheck method call in TLCServer
	pointcut callToModelCheckMethod(TLCServer aServer) : 
		call(void tlc2.tool.distributed.TLCServer.modelCheck(TLCServer)) && args(aServer);
	
	before(TLCServer aServer) : (callToModelCheckMethod(aServer)) {
		computationStartTime = new Date();
		server = aServer;
	}
}
