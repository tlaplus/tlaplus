package tlc2.tool.distributed;

import java.net.MalformedURLException;
import java.rmi.Naming;
import java.rmi.NoSuchObjectException;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.util.Date;
import java.util.Timer;
import java.util.TimerTask;
import java.util.logging.Level;
import java.util.logging.Logger;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.distributed.TLCWorker.TLCWorkerRunnable;

/**
 * Periodically checks if the server is still alive and exits the worker otherwise
 */
public class TLCTimerTask extends TimerTask {
	private final static Logger LOGGER = Logger.getLogger(TLCTimerTask.class.getName());

	private static final int TIMEOUT = Integer.getInteger(TLCTimerTask.class.getName() + ".timeout", 60) * 1000;

	private final String serverUrl;
	private final TLCWorkerRunnable[] runnables;
	private final Timer timer;

	public TLCTimerTask(final Timer keepAliveTimer, final TLCWorkerRunnable[] runnables, final String anUrl) {
		this.timer = keepAliveTimer;
		this.runnables = runnables;
		this.serverUrl = anUrl;
	}

	/* (non-Javadoc)
	 * @see java.util.TimerTask#run()
	 */
	public void run() {
		
		long lastInvocation = getMostRecentInvocation();
		long now = new Date().getTime();
		if(lastInvocation == 0 || (now - lastInvocation) > TIMEOUT) {
			try {
				final TLCServerRMI server = (TLCServerRMI) Naming.lookup(serverUrl);
				if(server.isDone()) {
					exitWorker(null);
				}
			} catch (MalformedURLException e) {
				// not expected to happen
				LOGGER.log(Level.FINEST, "Failed to exit worker", e);
			} catch (RemoteException e) {
				exitWorker(e);
			} catch (NotBoundException e) {
				exitWorker(e);
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

	private void exitWorker(Throwable e) {
		if (e != null) {
			MP.printError(EC.TLC_DISTRIBUTED_SERVER_NOT_RUNNING, e);
		} else {
			MP.printError(EC.TLC_DISTRIBUTED_SERVER_FINISHED);
		}
		for (int i = 0; i < runnables.length; i++) {
			try {
				TLCWorkerRunnable runnable = runnables[i];
				runnable.getTLCWorker().exit();
			} catch (NoSuchObjectException ex) {
				// not expected to happen
				LOGGER.log(Level.FINEST, "Failed to exit worker", ex);
			}
		}
		// Cancel this time after having exited the worker. Otherwise we keep on
		// going forever.
		this.timer.cancel();
	}
}
