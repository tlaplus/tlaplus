// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:29 PST by lamport
//      modified on Sat Aug  4 01:11:06 PDT 2001 by yuanyu

package tlc2.tool.distributed;

import java.io.File;
import java.io.IOException;
import java.net.InetAddress;
import java.rmi.NotBoundException;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.rmi.server.UnicastRemoteObject;
import java.util.Date;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCState;
import tlc2.tool.TLCTrace;
import tlc2.tool.WorkerException;
import tlc2.tool.fp.DiskFPSet;
import tlc2.tool.fp.FPSet;
import tlc2.tool.queue.DiskStateQueue;
import tlc2.tool.queue.StateQueue;
import tlc2.util.FP64;
import util.FileUtil;
import util.ToolIO;
import util.UniqueString;

/**
 * 
 * @version $Id$
 * @deprecated RMI related code, not used
 */
public class TLCServer extends UnicastRemoteObject implements TLCServerRMI,
		InternRMI {
	public FPSetManager fpSetManager;
	public FPSet fpSet;
	public StateQueue stateQueue;
	public TLCTrace trace;

	private TLCState errState = null;
	private boolean done = false;
	private boolean keepCallStack = false;
	private int thId = 0;
	private int workerCnt = 0, threadCnt = 0;
	private String metadir;
	private String filename;
	private DistApp work;
	private TLCWorkerRMI[] workers;
	private int[] workerRefCnt;
	private TLCServerThread[] threads;

	public TLCServer(DistApp work) throws IOException, NotBoundException {
		this.workers = new TLCWorkerRMI[10];
		this.workerRefCnt = new int[this.workers.length];
		this.threads = new TLCServerThread[10];
		this.metadir = work.getMetadir();
		int end = this.metadir.length();
		if (this.metadir.endsWith(FileUtil.separator))
			end--;
		int start = this.metadir.lastIndexOf(FileUtil.separator, end - 1);
		this.filename = this.metadir.substring(start + 1, end);
		this.work = work;
		this.stateQueue = new DiskStateQueue(this.metadir);
		this.trace = new TLCTrace(this.metadir, this.work.getFileName(),
				this.work);
		if (TLCGlobals.fpServers == null) {
			this.fpSet = new DiskFPSet(-1);
			this.fpSet.init(0, this.metadir, this.work.getFileName());
			this.fpSetManager = new FPSetManager((FPSetRMI) this.fpSet);
		} else {
			this.fpSetManager = new FPSetManager(TLCGlobals.fpServers);
		}
	}

	public final String getAppName() {
		return this.work.getAppName();
	}

	public final Boolean getCheckDeadlock() {
		return this.work.getCheckDeadlock();
	}

	public final Boolean getPreprocess() {
		return this.work.getPreprocess();
	}

	public final FPSetManager getFPSetManager() {
		return this.fpSetManager;
	}

	public final long getIrredPolyForFP() {
		return FP64.getIrredPoly();
	}

	public final UniqueString intern(String str) {
		// SZ 11.04.2009: changed access method
		return UniqueString.uniqueStringOf(str);
	}

	public synchronized final void registerWorker(TLCWorkerRMI worker,
			String hostname) throws IOException {
		int widx = this.workerCnt;
		int len = this.workers.length;

		if (widx >= len) {
			TLCWorkerRMI[] newWorkers = new TLCWorkerRMI[len * 2];
			int[] newWorkerRefCnt = new int[len * 2];
			for (int i = 0; i < len; i++) {
				newWorkers[i] = this.workers[i];
				newWorkerRefCnt[i] = this.workerRefCnt[i];
			}
			this.workers = newWorkers;
			this.workerRefCnt = newWorkerRefCnt;
			widx = len;
		}
		this.workerCnt++;
		this.workers[widx] = worker;
		this.workerRefCnt[widx] = 1;

		int tidx = this.threadCnt;
		len = this.threads.length;
		if (this.threadCnt >= len) {
			TLCServerThread[] newThreads = new TLCServerThread[len * 2];
			for (int i = 0; i < len; i++) {
				newThreads[i] = this.threads[i];
			}
			this.threads = newThreads;
			tidx = len;
		}
		this.threadCnt++;
		this.threads[tidx] = new TLCServerThread(this.thId++, worker, this);
		if (TLCGlobals.fpServers == null)
			this.fpSet.addThread();
		this.threads[tidx].start();

		ToolIO.out.println("Registration for worker at " + hostname
				+ " completed.");
	}

	/**
	 * Reassign a server thread to a new worker if there is available worker.
	 * For the current faulting worker, remove it if there is no reference to it
	 * any more.
	 */
	public synchronized final boolean reassignWorker(TLCServerThread th) {
		TLCWorkerRMI worker = th.getWorker();
		int widx;
		for (widx = 0; widx < this.workerCnt; widx++) {
			if (this.workers[widx] == worker)
				break;
		}
		if (widx >= this.workerCnt)
			return false;
		// reassign to a new worker:
		boolean success = false;
		if (this.workerCnt > 1) {
			int offset = (int) Math.floor(Math.random() * (this.workerCnt - 1));
			int widx1 = (widx + 1 + offset) % this.workerCnt;
			th.setWorker(this.workers[widx1]);
			this.workerRefCnt[widx1]++;
			success = true;
		}
		// remove the current faulting worker if possible:
		this.workerRefCnt[widx]--;
		if (this.workerRefCnt[widx] == 0) {
			for (int i = widx + 1; i < this.workerCnt; i++) {
				this.workers[i - 1] = this.workers[i];
				this.workerRefCnt[i - 1] = this.workerRefCnt[i];
			}
			this.workerCnt--;
		}
		return success;
	}

	public synchronized final boolean setErrState(TLCState s, boolean keep) {
		if (this.done)
			return false;
		this.done = true;
		this.errState = s;
		this.keepCallStack = keep;
		return true;
	}

	public final void setDone() {
		this.done = true;
	}

	public void checkpoint() throws IOException, InterruptedException {
		if (this.stateQueue.suspendAll()) {
			// Checkpoint:
			ToolIO.out.print("-- Checkpointing of run " + this.metadir
					+ " compl");

			// start checkpointing:
			this.stateQueue.beginChkpt();
			this.trace.beginChkpt();
			if (this.fpSet == null) {
				this.fpSetManager.checkpoint(this.filename);
			} else {
				this.fpSet.beginChkpt();
			}
			this.stateQueue.resumeAll();
			UniqueString.internTbl.beginChkpt(this.metadir);
			// commit:
			this.stateQueue.commitChkpt();
			this.trace.commitChkpt();
			UniqueString.internTbl.commitChkpt(this.metadir);
			if (this.fpSet != null) {
				this.fpSet.commitChkpt();
			}
			ToolIO.out.println("eted.");
		}
	}

	public final void recover() throws IOException, InterruptedException {
		this.trace.recover();
		this.stateQueue.recover();
		if (this.fpSet == null) {
			this.fpSetManager.recover(this.filename);
		} else {
			this.fpSet.recover();
		}
	}

	private final String recoveryStats() throws IOException {
		return (this.fpSetManager.size() + " distinct states found. "
				+ this.stateQueue.size() + " states on queue.");
	}

	public final String stats() throws IOException {
		return (this.fpSetManager.size() + " distinct states found. "
				+ this.stateQueue.size() + " states left on queue.");
	}

	private final void doInit() throws Exception {
		TLCState curState = null;
		try {
			TLCState[] initStates = work.getInitStates();
			for (int i = 0; i < initStates.length; i++) {
				curState = initStates[i];
				boolean inConstraints = work.isInModel(curState);
				boolean seen = false;
				if (inConstraints) {
					long fp = curState.fingerPrint();
					seen = this.fpSetManager.put(fp);
					if (!seen) {
						initStates[i].uid = trace.writeState(1, fp);
						stateQueue.enqueue(initStates[i]);
					}
				}
				if (!inConstraints || !seen) {
					work.checkState(null, curState);
				}
			}
		} catch (Exception e) {
			this.errState = curState;
			this.keepCallStack = true;
			if (e instanceof WorkerException) {
				this.errState = ((WorkerException) e).state2;
				this.keepCallStack = ((WorkerException) e).keepCallStack;
			}
			this.done = true;
			throw e;
		}
	}

	private final void close(boolean cleanup) throws IOException {
		this.trace.close();
		if (this.fpSet == null) {
			this.fpSetManager.close(cleanup);
		} else {
			this.fpSet.close();
		}
		if (cleanup) {
			FileUtil.deleteDir(new File(this.metadir), true);
		}
	}

	public static int Port = 10997; // the port # for tlc server

	public static void modelCheck(TLCServer server) throws Exception {
		boolean recovered = false;
		if (server.work.canRecover()) {
			ToolIO.out.println("-- Starting recovery from checkpoint "
					+ server.metadir);
			server.recover();
			ToolIO.out.println("-- Recovery completed. "
					+ server.recoveryStats());
			recovered = true;
		}
		if (!recovered) {
			// Initialize with the initial states:
			try {
				server.doInit();
			} catch (Throwable e) {
				// Assert.printStack(e);
				server.done = true;
				ToolIO.out.println(e.getMessage());
				if (server.errState != null) {
					ToolIO.out.println("While working on the initial state:");
					ToolIO.out.println(server.errState);
				}
				// We redo the work on the error state, recording the call
				// stack.
				server.work.setCallStack();
				try {
					server.doInit();
				} catch (Throwable e1) {
					ToolIO.out
							.println("The error occurred when TLC was evaluating the nested"
									+ "\nexpressions at the following positions:\n"
									+ server.work.printCallStack());
				}
			}
		}
		if (server.done) {
			// clean up before exit:
			server.close(false);
			System.exit(0);
		}

		String hostname = InetAddress.getLocalHost().getHostName();
		Registry rg = LocateRegistry.createRegistry(Port);
		rg.rebind("TLCServer", server);
		ToolIO.out.println("TLC server at " + hostname + " is ready.");

		// Wait for completion, but print out progress report and checkpoint
		// periodically.
		long lastChkpt = System.currentTimeMillis();
		synchronized (server) {
			server.wait(30000);
		}
		while (true) {
			long now = System.currentTimeMillis();
			if (now - lastChkpt >= TLCGlobals.chkptDuration) {
				server.checkpoint();
				lastChkpt = now;
			}
			synchronized (server) {
				if (!server.done) {
					ToolIO.out.println("Progress(" + server.trace.getLevel()
							+ "): " + server.stats());
					server.wait(300000);
				}
				if (server.done)
					break;
			}
		}
		// Wait for all the server threads to die.
		for (int i = 0; i < server.threadCnt; i++) {
			server.threads[i].join();
		}
		// Notify all the workers of the completion.
		for (int i = 0; i < server.workerCnt; i++) {
			try {
				server.workers[i].exit();
			} catch (Exception e) { /* SKIP */
			}
		}
		// Postprocessing:
		boolean success = (server.errState == null);
		if (success) {
			// We get here because the checking has succeeded.
			ToolIO.out
					.println("Model checking completed. No error has been found at: "
							+ new Date());
		} else if (server.keepCallStack) {
			// We redo the work on the error state, recording the call stack.
			server.work.setCallStack();
			try {
				// server.doNext();
			} catch (Exception e) {
				ToolIO.out
						.println("The error occurred when TLC was evaluating the nested"
								+ "\nexpressions at the following positions:");
				server.work.printCallStack();
			}
		}
		ToolIO.out.println(server.stats());

		server.close(success);

		ToolIO.out.println("Server has finished computing at: " + new Date());
		ToolIO.out.flush();

		// MAK commenting it to let the runtime finish normally
		// System.exit(0);
	}

	public static void main(String argv[]) {
		ToolIO.out.println("TLC Server " + TLCGlobals.versionOfTLC);
		TLCServer server = null;
		try {
			TLCGlobals.fpServers = TLCConfig.getStringArray("fp_servers");
			TLCGlobals.setNumWorkers(0);
			server = new TLCServer(TLCApp.create(argv));
			modelCheck(server);
		} catch (Throwable e) {
			System.gc();
			// Assert.printStack(e);
			if (e instanceof StackOverflowError) {
				MP.printError(EC.SYSTEM_STACK_OVERFLOW);
			} else if (e instanceof OutOfMemoryError) {
				MP.printError(EC.SYSTEM_OUT_OF_MEMORY);
			} else {
				MP.printError(EC.GENERAL, e);
			}
			if (server != null) {
				try {
					server.close(false);
				} catch (Exception e1) { /* SKIP */
				}
			}
		}
		System.exit(0);
	}
}
