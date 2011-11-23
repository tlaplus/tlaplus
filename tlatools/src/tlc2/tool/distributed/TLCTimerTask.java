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

/**
 * Periodically checks if the server is still alive and exists the worker otherwise
 */
public class TLCTimerTask extends TimerTask {

	private final String serverUrl;
	private final TLCWorker worker;

	public TLCTimerTask(final TLCWorker aWorker, final String anUrl) {
		worker = aWorker;
		serverUrl = anUrl;
	}

	/* (non-Javadoc)
	 * @see java.util.TimerTask#run()
	 */
	public void run() {
		long lastInvocation = worker.getLastInvocation();
		long now = new Date().getTime();
		if(lastInvocation == 0 || (now - lastInvocation) > 60000) {
			try {
				final TLCServerRMI server = (TLCServerRMI) Naming.lookup(serverUrl);
				if(server.isDone()) {
					exitWorker();
				}
			} catch (MalformedURLException e) {
				// not expected to happen
				e.printStackTrace();
			} catch (RemoteException e) {
				exitWorker();
			} catch (NotBoundException e) {
				exitWorker();
			}
		}
	}

	private void exitWorker() {
		MP.printError(EC.TLC_DISTRIBUTED_SERVER_NOT_RUNNING);
		try {
			worker.exit();
		} catch (NoSuchObjectException e) {
			// not expected to happen
			e.printStackTrace();
		}
	}
}
