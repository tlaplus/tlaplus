package tlc2.tool.distributed;

import java.net.MalformedURLException;
import java.rmi.Naming;
import java.rmi.NoSuchObjectException;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.util.Date;
import java.util.TimerTask;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.distributed.TLCWorker.TLCWorkerRunnable;

/**
 * Periodically checks if the server is still alive and exists the worker otherwise
 */
public class TLCTimerTask extends TimerTask {

	private final String serverUrl;
	private final TLCWorkerRunnable[] runnables;

	public TLCTimerTask(final TLCWorkerRunnable[] runnables, final String anUrl) {
		this.runnables = runnables;
		serverUrl = anUrl;
	}

	/* (non-Javadoc)
	 * @see java.util.TimerTask#run()
	 */
	public void run() {
		
		long lastInvocation = getMostRecentInvocation();
		long now = new Date().getTime();
		if(lastInvocation == 0 || (now - lastInvocation) > 60000) {
			try {
				final TLCServerRMI server = (TLCServerRMI) Naming.lookup(serverUrl);
				if(server.isDone()) {
					exitWorker();
				}
			} catch (MalformedURLException e) {
				// not expected to happen
				MP.printError(EC.GENERAL, e);
			} catch (RemoteException e) {
				exitWorker();
			} catch (NotBoundException e) {
				exitWorker();
			}
		}
	}

	private long getMostRecentInvocation() {
		long minInvocation = 0L;
		for (int i = 0; i < runnables.length; i++) {
			TLCWorkerRunnable runnable = runnables[i];
			long lastInvocation = runnable.getTLCWorker().getLastInvocation();
			minInvocation = Math.max(minInvocation, lastInvocation);
		}
		return minInvocation;
	}

	private void exitWorker() {
		MP.printError(EC.TLC_DISTRIBUTED_SERVER_NOT_RUNNING);
		try {
			for (int i = 0; i < runnables.length; i++) {
				TLCWorkerRunnable runnable = runnables[i];
				runnable.getTLCWorker().exit();
			}
		} catch (NoSuchObjectException e) {
			// not expected to happen
		    // LL modified error message on 7 April 2012
			MP.printError(EC.GENERAL, "trying to exit a worker", e);
		}
	}
}
