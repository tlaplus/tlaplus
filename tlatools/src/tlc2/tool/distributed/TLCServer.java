// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:29 PST by lamport
//      modified on Sat Aug  4 01:11:06 PDT 2001 by yuanyu

package tlc2.tool.distributed;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.net.InetAddress;
import java.net.URI;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.rmi.server.UnicastRemoteObject;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.CyclicBarrier;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.ModelChecker;
import tlc2.tool.TLCState;
import tlc2.tool.TLCTrace;
import tlc2.tool.WorkerException;
import tlc2.tool.distributed.fp.DynamicFPSetManager;
import tlc2.tool.distributed.fp.FPSetRMI;
import tlc2.tool.distributed.fp.IFPSetManager;
import tlc2.tool.distributed.fp.StaticFPSetManager;
import tlc2.tool.distributed.management.TLCServerMXWrapper;
import tlc2.tool.distributed.selector.BlockSelectorFactory;
import tlc2.tool.distributed.selector.IBlockSelector;
import tlc2.tool.fp.FPSet;
import tlc2.tool.management.TLCStandardMBean;
import tlc2.tool.queue.DiskStateQueue;
import tlc2.tool.queue.IStateQueue;
import tlc2.util.FP64;
import util.Assert;
import util.FileUtil;
import util.UniqueString;

@SuppressWarnings("serial")
public class TLCServer extends UnicastRemoteObject implements TLCServerRMI,
		InternRMI {

	/**
	 * the port # for tlc server
	 */
	public static int Port = Integer.getInteger(TLCServer.class.getName() + ".port", 10997);


	/**
	 * show statistics every 1 minutes
	 */
	private static final int REPORT_INTERVAL = Integer.getInteger(TLCServer.class.getName() + ".report", 1 * 60 * 1000);

	/**
	 * If the state/ dir should be cleaned up after a successful model run
	 */
	private static final boolean VETO_CLEANUP = Boolean.getBoolean(TLCServer.class.getName() + ".vetoCleanup");
	
	/**
	 * Performance metric: distinct states per minute
	 */
	private long distinctStatesPerMinute;
	/**
	 * Performance metric: states per minute
	 */
	private long statesPerMinute;

	public final IFPSetManager fpSetManager;
	public final IStateQueue stateQueue;
	public final TLCTrace trace;

	private final DistApp work;
	private final String metadir;
	private final String filename;

	public FPSet fpSet;

	private TLCState errState = null;
	private boolean done = false;
	private boolean keepCallStack = false;
	private int thId = 0;
	
	private final Map<TLCServerThread, TLCWorkerRMI> threadsToWorkers = new HashMap<TLCServerThread, TLCWorkerRMI>();
	
	private final CyclicBarrier barrier;
	private final IBlockSelector blockSelector;


	static final int expectedWorkerCount = Integer.getInteger(TLCServer.class.getName() + ".expectedWorkerCount", 1);
	/**
	 * 
	 */
	private final CountDownLatch latch;
	static final int expectedFPSetCount = Integer.getInteger(TLCServer.class.getName() + ".expectedFPSetCount", 0);
	
	/**
	 * @param work
	 * @throws IOException
	 * @throws NotBoundException
	 */
	public TLCServer(TLCApp work) throws IOException, NotBoundException {
	    // LL modified error message on 7 April 2012
		Assert.check(work != null, "TLC server found null work.");
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
		if (TLCGlobals.fpServers == null && expectedFPSetCount <= 0) {
			this.fpSet = FPSet.getFPSet(work.getFPBits(), work.getFpMemSize());
			this.fpSet.init(0, this.metadir, this.work.getFileName());
			this.fpSetManager = new StaticFPSetManager((FPSetRMI) this.fpSet);
		} else if (expectedFPSetCount > 0) {
			this.fpSetManager = new DynamicFPSetManager(expectedFPSetCount);
		} else {
			this.fpSetManager = new StaticFPSetManager(TLCGlobals.fpServers);
		}
		barrier = new CyclicBarrier(expectedWorkerCount);
		latch = new CountDownLatch(expectedFPSetCount);
		blockSelector = BlockSelectorFactory.getBlockSelector(this);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServerRMI#getCheckDeadlock()
	 */
	public final Boolean getCheckDeadlock() {
		return this.work.getCheckDeadlock();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServerRMI#getPreprocess()
	 */
	public final Boolean getPreprocess() {
		return this.work.getPreprocess();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServerRMI#getFPSetManager()
	 */
	public final IFPSetManager getFPSetManager() {
		try {
			latch.await();
		} catch (InterruptedException e) {
			e.printStackTrace();
		}
		return this.fpSetManager;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServerRMI#getIrredPolyForFP()
	 */
	public final long getIrredPolyForFP() {
		return FP64.getIrredPoly();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.InternRMI#intern(java.lang.String)
	 */
	public final UniqueString intern(String str) {
		// SZ 11.04.2009: changed access method
		return UniqueString.uniqueStringOf(str);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServerRMI#registerWorker(tlc2.tool.distributed.TLCWorkerRMI)
	 */
	public synchronized final void registerWorker(TLCWorkerRMI worker
			) throws IOException {
		
		// Wake up potentially stuck TLCServerThreads (in
		// tlc2.tool.queue.StateQueue.isAvail()) to avoid a deadlock.
		// Obviously stuck TLCServerThreads will never be reported to 
		// users if resumeAllStuck() is not call by a new worker.
		stateQueue.resumeAllStuck();
		
		// create new server thread for given worker
		final TLCServerThread thread = new TLCServerThread(this.thId++, worker, this, barrier, blockSelector);
		threadsToWorkers.put(thread, worker);
		if (TLCGlobals.fpServers == null && expectedFPSetCount <= 0) {
			this.fpSet.addThread();
		}
		thread.start();

		MP.printMessage(EC.TLC_DISTRIBUTED_WORKER_REGISTERED, worker.getURI().toString());
	}

	public synchronized void registerFPSet(FPSetRMI fpSet, String hostname) throws RemoteException {
		this.fpSetManager.register(fpSet, hostname);
		latch.countDown();
	}

	/**
	 * An (idempotent) method to remove a (dead) TLCServerThread from the TLCServer.
	 * 
	 * @see Map#remove(Object)
	 * @param thread
	 * @return 
	 */
	public synchronized TLCWorkerRMI removeTLCServerThread(final TLCServerThread thread) {
		final TLCWorkerRMI worker = threadsToWorkers.remove(thread);
		/*
		 * Only ever report a disconnected worker once!
		 * 
		 * Calling this method twice happens when the exception handling in
		 * TLCServerThread#run detects a disconnect server and the
		 * TLCServerThread#TimerTask (who periodically checks worker aliveness)
		 * again.
		 * 
		 * (TimerTask cancellation in TLCServerThread#run has a small chance of
		 * leaving the TimerTask running. This occurs by design if the TimerTask
		 * has already been marked for execution)
		 * 
		 * @see https://bugzilla.tlaplus.net/show_bug.cgi?id=216
		 */
		if (worker != null) {
			MP.printMessage(EC.TLC_DISTRIBUTED_WORKER_DEREGISTERED, thread.getUri().toString());
		}
		return worker;
	}

	/**
	 * @param s
	 * @param keep
	 * @return
	 */
	public synchronized final boolean setErrState(TLCState s, boolean keep) {
		if (this.done)
			return false;
		this.done = true;
		this.errState = s;
		this.keepCallStack = keep;
		return true;
	}

	/**
	 * 
	 */
	public final void setDone() {
		this.done = true;
	}

	/**
	 * Creates a checkpoint for the currently running model run
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public void checkpoint() throws IOException, InterruptedException {
		if (this.stateQueue.suspendAll()) {
			// Checkpoint:
			MP.printMessage(EC.TLC_CHECKPOINT_START, "-- Checkpointing of run " + this.metadir
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
			MP.printMessage(EC.TLC_CHECKPOINT_END, "eted.");
		}
	}

	/**
	 * Recovers a model run
	 * @throws IOException
	 * @throws InterruptedException
	 */
	public final void recover() throws IOException, InterruptedException {
		this.trace.recover();
		this.stateQueue.recover();
		if (this.fpSet == null) {
			this.fpSetManager.recover(this.filename);
		} else {
			this.fpSet.recover();
		}
	}

	/**
	 * @throws Exception
	 */
	private final Set<Long> doInit() throws Exception {
		final SortedSet<Long> set = new TreeSet<Long>();
		TLCState curState = null;
		try {
			TLCState[] initStates = work.getInitStates();
			for (int i = 0; i < initStates.length; i++) {
				curState = initStates[i];
				boolean inConstraints = work.isInModel(curState);
				boolean seen = false;
				if (inConstraints) {
					long fp = curState.fingerPrint();
					seen = !set.add(fp);
					if (!seen) {
						initStates[i].uid = trace.writeState(fp);
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
		return set;
	}

	/**
	 * @param cleanup
	 * @throws IOException
	 */
	public final void close(boolean cleanup) throws IOException {
		this.trace.close();
		if (this.fpSet == null) {
			this.fpSetManager.close(cleanup);
		} else {
			this.fpSet.close();
		}
		if (cleanup && !VETO_CLEANUP) {
			FileUtil.deleteDir(new File(this.metadir), true);
		}
	}

	/**
	 * @param server
	 * @throws IOException
	 * @throws InterruptedException
	 * @throws NotBoundException
	 */
	public static void modelCheck(TLCServer server) throws IOException, InterruptedException, NotBoundException {
		boolean recovered = false;
		if (server.work.canRecover()) {
            MP.printMessage(EC.TLC_CHECKPOINT_RECOVER_START, server.metadir);
			server.recover();
			MP.printMessage(EC.TLC_CHECKPOINT_RECOVER_END, new String[] { String.valueOf(server.fpSet.size()),
                    String.valueOf(server.stateQueue.size())});
			recovered = true;
		}
		Set<Long> initFPs = new TreeSet<Long>();
		if (!recovered) {
			// Initialize with the initial states:
			try {
                MP.printMessage(EC.TLC_COMPUTING_INIT);
                initFPs = server.doInit();
				MP.printMessage(EC.TLC_INIT_GENERATED1,
						new String[] { String.valueOf(server.stateQueue.size()), "(s)" });
			} catch (Throwable e) {
				// Assert.printStack(e);
				server.done = true;
				// LL modified error message on 7 April 2012
				MP.printError(EC.GENERAL, "initializing the server", e); // LL changed call 7 April 2012
				if (server.errState != null) {
					MP.printMessage(EC.TLC_INITIAL_STATE, "While working on the initial state: " + server.errState);
				}
				// We redo the work on the error state, recording the call
				// stack.
				server.work.setCallStack();
				try {
					initFPs = server.doInit();
				} catch (Throwable e1) {
					MP.printError(EC.GENERAL, "evaluating the nested"   // LL changed call 7 April 2012
									+ "\nexpressions at the following positions:\n"
									+ server.work.printCallStack(), e);
				}
			}
		}
		if (server.done) {
			// clean up before exit:
			server.close(false);
			return;
		}

		String hostname = InetAddress.getLocalHost().getHostName();
		Registry rg = LocateRegistry.createRegistry(Port);
		rg.rebind("TLCServer", server);
		MP.printMessage(EC.TLC_DISTRIBUTED_SERVER_RUNNING, hostname);
		
		// First register TLCSERVER with RMI and only then wait for all FPSets to become registered
		server.latch.await();
		for (Long fp : initFPs) {
			server.fpSetManager.put(fp);
		}

		// Wait for completion, but print out progress report and checkpoint
		// periodically.
		synchronized (server) {
			server.wait(REPORT_INTERVAL);
		}
		long oldNumOfGenStates = 0;
        long oldFPSetSize = 0;
		while (true) {
			if (TLCGlobals.doCheckPoint()) {
				server.checkpoint();
			}
			synchronized (server) {
				if (!server.done) {
					final long numOfGenStates = server.getStatesComputed();
					final long fpSetSize = server.fpSetManager.size();
					
			        // print progress showing states per minute metric (spm)
			        final double factor = REPORT_INTERVAL / 60000d;
					server.statesPerMinute = (long) ((numOfGenStates - oldNumOfGenStates) / factor);
					server.distinctStatesPerMinute = (long) ((fpSetSize - oldFPSetSize) / factor);
			        
					// print to system.out
					MP.printMessage(EC.TLC_PROGRESS_STATS, new String[] { String.valueOf(server.trace.getLevelForReporting()),
			                String.valueOf(numOfGenStates), String.valueOf(fpSetSize),
			                String.valueOf(server.getNewStates()), String.valueOf(server.statesPerMinute), String.valueOf(server.distinctStatesPerMinute) });
					server.wait(REPORT_INTERVAL);
					
					// keep current values as old values
					oldFPSetSize = fpSetSize;
					oldNumOfGenStates = numOfGenStates;
				}
				if (server.done)
					break;
			}
		}
		// Wait for all the server threads to die.
		for (final Entry<TLCServerThread, TLCWorkerRMI> entry : server.threadsToWorkers.entrySet()) {
			final TLCServerThread thread = entry.getKey();
			
			thread.join();
			
			// print worker stats
			int sentStates = thread.getSentStates();
			int receivedStates = thread.getReceivedStates();
			URI name = thread.getUri();
			MP.printMessage(EC.TLC_DISTRIBUTED_WORKER_STATS,
					new String[] { name.toString(), Integer.toString(sentStates), Integer.toString(receivedStates) });

			final TLCWorkerRMI worker = entry.getValue();
			try {
				worker.exit();
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		
		server.statesPerMinute = 0;
		server.distinctStatesPerMinute = 0;
		
		// Postprocessing:
		boolean success = (server.errState == null);
		if (success && server.fpSet != null) {
			// We get here because the checking has succeeded.
			ModelChecker.reportSuccess(server.fpSet, server.fpSetManager.size());
		} else if (success && server.fpSet == null) {
	        final long d = server.fpSetManager.size();
	        final double actualProb = server.fpSetManager.checkFPs();
			ModelChecker.reportSuccess(d, actualProb, server.fpSetManager.getStatesSeen());
		} else if (server.keepCallStack) {
			// We redo the work on the error state, recording the call stack.
			server.work.setCallStack();
			try {
				// server.doNext();
			} catch (Exception e) {
				MP.printMessage(EC.TLC_NESTED_EXPRESSION, "The error occurred when TLC was evaluating the nested"
								+ "\nexpressions at the following positions:");
				server.work.printCallStack();
			}
		}

		server.printSummary(success);

		server.close(success);
		
		// dispose RMI leftovers
		rg.unbind("TLCServer");
		if (server.fpSet != null) {
			server.fpSet.unexportObject(false);
		}
		UnicastRemoteObject.unexportObject(server, false);
		
        MP.printMessage(EC.TLC_FINISHED);
		MP.flush();
	}
	
	public long getStatesGeneratedPerMinute() {
		return statesPerMinute;
	}
	
	public long getDistinctStatesGeneratedPerMinute() {
		return distinctStatesPerMinute;
	}


	/**
	 * @return
	 */
	public synchronized long getNewStates() {
		long res = stateQueue.size();
		for (TLCServerThread thread : threadsToWorkers.keySet()) {
			res += thread.getCurrentSize();
		}
		return res;
	}

	// use fingerprint server to determine how many states have been calculated
    public long getStatesComputed() throws RemoteException {
    	return fpSetManager.getStatesSeen();
	}

	// query each worker for how many states computed (workers might disconnect)
//    private long getStatesComputed() throws RemoteException {
//    	long res = 0L;
//		for (int i = 0; i < workerCnt; i++) {
//			res += workers[i].getStatesComputed();
//		}
//		return res;
//	}
    
    /**
     * This allows the toolbox to easily display the last set
     * of state space statistics by putting them in the same
     * form as all other progress statistics.
     */
    public final void printSummary(boolean success) throws IOException
    {
        long statesGenerated = this.getStatesComputed();
		long distinctStates = this.fpSetManager.size();
		long statesLeftInQueue = this.getNewStates();
		int level = this.trace.getLevelForReporting();
		if (TLCGlobals.tool) {
            MP.printMessage(EC.TLC_PROGRESS_STATS, new String[] { String.valueOf(level),
                    String.valueOf(statesGenerated), String.valueOf(distinctStates),
                    String.valueOf(statesLeftInQueue), "0", "0" });
        }

        MP.printMessage(EC.TLC_STATS, new String[] { String.valueOf(statesGenerated),
                String.valueOf(distinctStates), String.valueOf(statesLeftInQueue) });
        if (success) {
            MP.printMessage(EC.TLC_SEARCH_DEPTH, String.valueOf(level));
        }
    }

	public static void main(String argv[]) {
		MP.printMessage(EC.GENERAL, "TLC Server " + TLCGlobals.versionOfTLC);
		TLCStandardMBean tlcServerMXWrapper = TLCStandardMBean.getNullTLCStandardMBean();
		TLCServer server = null;
		try {
			final String fpServerProperty = System.getProperty("fp_servers");
			if(fpServerProperty != null) {
				String[] fpServers = fpServerProperty.split(",");
				TLCGlobals.fpServers = fpServers;
			}
			TLCGlobals.setNumWorkers(0);
			server = new TLCServer(TLCApp.create(argv));
			tlcServerMXWrapper = new TLCServerMXWrapper(server);
			if(server != null) {
				Runtime.getRuntime().addShutdownHook(new Thread(new WorkerShutdownHook(server)));
				modelCheck(server);
			}
		} catch (Throwable e) {
			System.gc();
			// Assert.printStack(e);
			if (e instanceof StackOverflowError) {
				MP.printError(EC.SYSTEM_STACK_OVERFLOW, e);
			} else if (e instanceof OutOfMemoryError) {
				MP.printError(EC.SYSTEM_OUT_OF_MEMORY, e);
			} else {
				MP.printError(EC.GENERAL, e);
			}
			if (server != null) {
				try {
					server.close(false);
				} catch (Exception e1) {
					e1.printStackTrace();
				}
			}
		} finally {
			tlcServerMXWrapper.unregister();
		}
	}

	/**
	 * @return Number of currently registered workers
	 */
	public int getWorkerCount() {
		return threadsToWorkers.size();
	}
	
	/**
	 * @return
	 */
	synchronized TLCServerThread[] getThreads() {
		return threadsToWorkers.keySet().toArray(new TLCServerThread[threadsToWorkers.size()]);
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServerRMI#isDone()
	 */
	public boolean isDone() throws RemoteException {
		return done;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServerRMI#getSpec()
	 */
	public String getSpecFileName() throws RemoteException {
		return this.work.getFileName();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServerRMI#getConfig()
	 */
	public String getConfigFileName() throws RemoteException {
		return this.work.getConfigName();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCServerRMI#getFile(java.lang.String)
	 */
	public byte[] getFile(final String file) throws RemoteException {
		// sanitize file to only last part of the path
		// to make sure to not load files outside of spec dir
		String name = new File(file).getName();
		
		File f = new File(work.getSpecDir() + File.separator + name);
		return read(f);
	}
	
	private byte[] read(final File file) {
		if (file.isDirectory())
			throw new RuntimeException("Unsupported operation, file "
					+ file.getAbsolutePath() + " is a directory");
		if (file.length() > Integer.MAX_VALUE)
			throw new RuntimeException("Unsupported operation, file "
					+ file.getAbsolutePath() + " is too big");

		Throwable pending = null;
		FileInputStream in = null;
		final byte buffer[] = new byte[(int) file.length()];
		try {
			in = new FileInputStream(file);
			in.read(buffer);
		} catch (Exception e) {
			pending = new RuntimeException("Exception occured on reading file "
					+ file.getAbsolutePath(), e);
		} finally {
			if (in != null) {
				try {
					in.close();
				} catch (Exception e) {
					if (pending == null) {
						pending = new RuntimeException(
								"Exception occured on closing file"
										+ file.getAbsolutePath(), e);
					}
				}
			}
			if (pending != null) {
				throw new RuntimeException(pending);
			}
		}
		return buffer;
	}
	

	/**
	 * Tries to exit all connected workers
	 */
	private static class WorkerShutdownHook implements Runnable {
		
		private final TLCServer server;
		
		public WorkerShutdownHook(final TLCServer aServer) {
			server = aServer;
		}

		/* (non-Javadoc)
		 * @see java.lang.Runnable#run()
		 */
		public void run() {
			for (TLCWorkerRMI worker : server.threadsToWorkers.values()) {
				try {
					if(worker != null) {
						worker.exit();
					}
				} catch (java.rmi.ConnectException e)  {
					// happens if worker has exited already
				} catch (java.rmi.NoSuchObjectException e) {
					// happens if worker has exited already
				} catch (IOException e) {
					//TODO handle more gracefully
					e.printStackTrace();
				}
			}
		}
	}
}
