// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:40 PST by lamport  
//      modified on Thu May 31 13:24:56 PDT 2001 by yuanyu   

package tlc2.tool.distributed;

import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.InetAddress;
import java.net.URI;
import java.net.UnknownHostException;
import java.rmi.ConnectException;
import java.rmi.Naming;
import java.rmi.NoSuchObjectException;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.util.Date;
import java.util.HashSet;
import java.util.Set;
import java.util.Timer;
import java.util.TreeSet;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.RejectedExecutionException;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateVec;
import tlc2.tool.WorkerException;
import tlc2.tool.distributed.fp.IFPSetManager;
import tlc2.util.BitVector;
import tlc2.util.Cache;
import tlc2.util.FP64;
import tlc2.util.LongVec;
import tlc2.util.SimpleCache;
import util.Assert;
import util.ToolIO;
import util.UniqueString;
@SuppressWarnings("serial")
public class TLCWorker extends UnicastRemoteObject implements TLCWorkerRMI {

	private static final boolean unsorted = Boolean.getBoolean(TLCWorker.class.getName() + ".unsorted");
	
	private static Timer keepAliveTimer;
	private static RMIFilenameToStreamResolver fts;
	private static final ExecutorService executorService = Executors.newCachedThreadPool();
	private static TLCWorkerRunnable[] runnables = new TLCWorkerRunnable[0];
	
	private DistApp work;
	private IFPSetManager fpSetManager;
	private final URI uri;
	/**
	 * Indicate whether the worker is busy computing states
	 */
	private volatile boolean computing = false;
	private long lastInvocation;
	private long overallStatesComputed;
	
	private final Cache cache;
	

	public TLCWorker(final int threadId, DistApp work, IFPSetManager fpSetManager, String aHostname)
			throws RemoteException {
		this.work = work;
		this.fpSetManager = fpSetManager;
		this.uri = URI.create("rmi://" + aHostname + ":" + getPort() + "/"
				+ threadId);
		
		this.cache = new SimpleCache();
	}
	
	//TODO Remove once performance tests show superiority of TreeSet
	private Set<Holder> getSet() {
		if (unsorted) {
			return new HashSet<Holder>();
		} else {
			return new TreeSet<Holder>();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#getNextStates(tlc2.tool.TLCState[])
	 */
	public synchronized NextStateResult getNextStates(final TLCState[] states)
			throws WorkerException, RemoteException {
		
		computing = true;
		
		// statistics
		lastInvocation = System.currentTimeMillis();
		// Amount of states computed in this single invocation
		long statesComputed = 0L;
		
		TLCState state1 = null, state2 = null;
		try {
			TLCState[] nstates;
			final Set<Holder> treeSet = getSet();
			// Compute all of the next states of this block of states.
			for (int i = 0; i < states.length; i++) {
				state1 = states[i];
				nstates = this.work.getNextStates(state1);
				// Keep statistics about states computed during this invocation
				statesComputed += nstates.length;
				// add all succ states/fps to the array designated for the corresponding fp server
				for (int j = 0; j < nstates.length; j++) {
					long fp = nstates[j].fingerPrint();
					if (!cache.hit(fp)) {
						treeSet.add(new Holder(fp, nstates[j], state1));
					}
				}
			}
			
			// Amount of states computed in during all invocations
			overallStatesComputed += statesComputed;
			
			// create containers for each fingerprint _server_
			int fpServerCnt = this.fpSetManager.numOfServers();
			// previous state
			TLCStateVec[] pvv = new TLCStateVec[fpServerCnt];
			// container for all succ states
			TLCStateVec[] nvv = new TLCStateVec[fpServerCnt];
			// container for all succ state fingerprints
			final LongVec[] fpvv = new LongVec[fpServerCnt];
			for (int i = 0; i < fpServerCnt; i++) {
				pvv[i] = new TLCStateVec();
				nvv[i] = new TLCStateVec();
				fpvv[i] = new LongVec();
			}
			
			// Add elements of treeSet in sorted order to pvv, nvv, fpvv.
			// This is done hoping (not yet measured) that it will cause less
			// disk seeks at the fingerprint server since fingerprints are
			// ordered and thus two...n consecutive fingerprints reside on the
			// same disk page.
			//
			// Additionally we later might wanna optimize lock acquisition based
			// on the invariant of sorted fingerprints.
			long last = Long.MIN_VALUE;
			for (final Holder holder : treeSet) {
				// make sure invariant is followed
				long fp = holder.getFp();
				Assert.check(last < fp, EC.GENERAL);
				last = fp;

				int fpIndex = fpSetManager.getFPSetIndex(fp);
				pvv[fpIndex].addElement(holder.getParentState());
				nvv[fpIndex].addElement(holder.getNewState());
				fpvv[fpIndex].addElement(fp);
			}

			BitVector[] visited = this.fpSetManager.containsBlock(fpvv, executorService);

			// Remove the states that have already been seen, check if the
			// remaining new states are valid and inModel.
			TLCStateVec[] newStates = new TLCStateVec[fpServerCnt];
			LongVec[] newFps = new LongVec[fpServerCnt];
			for (int i = 0; i < fpServerCnt; i++) {
				newStates[i] = new TLCStateVec();
				newFps[i] = new LongVec();
			}

			for (int i = 0; i < fpServerCnt; i++) {
				BitVector.Iter iter = new BitVector.Iter(visited[i]);
				int index;
				while ((index = iter.next()) != -1) {
					state1 = pvv[i].elementAt(index);
					state2 = nvv[i].elementAt(index);
					this.work.checkState(state1, state2);
					if (this.work.isInModel(state2)
							&& this.work.isInActions(state1, state2)) {
						state2.uid = state1.uid;
						newStates[i].addElement(state2);
						newFps[i].addElement(fpvv[i].elementAt(index));
					}
				}
			}
			
			// Prepare the return value.
			final long computationTime = System.currentTimeMillis() - lastInvocation;
			return new NextStateResult(newStates, newFps, computationTime, statesComputed);
		} catch (WorkerException e) {
			throw e;
		} catch (OutOfMemoryError e) {
			throw new RemoteException("OutOfMemoryError occurred at worker: " + uri.toASCIIString(), e);
		} catch (RejectedExecutionException e) {
			throw new RemoteException("Executor rejected task at worker: " + uri.toASCIIString(), e);
		} catch (Throwable e) {
			throw new WorkerException(e.getMessage(), e, state1, state2, true);
		} finally {
			computing = false;
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#exit()
	 */
	public void exit() throws NoSuchObjectException {
		ToolIO.out.println(uri.getHost() + ", work completed at: " + new Date() + " Computed: "
				+ overallStatesComputed
				+ " and a cache hit ratio of " + this.cache.getHitRatioAsString()
				+ ", Thank you!");
		
		executorService.shutdown();
		
		keepAliveTimer.cancel();
		
		UnicastRemoteObject.unexportObject(TLCWorker.this, true);
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#isAlive()
	 */
	public boolean isAlive() {
		return true;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#getURI()
	 */
	public URI getURI() throws RemoteException {
		return uri;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.TLCWorkerRMI#getCacheRateRatio()
	 */
	public double getCacheRateRatio() throws RemoteException {
		return this.cache.getHitRatio();
	}
	
	private int getPort() {
		try {
			// this only works on >= Sun Java 1.6
//			sun.rmi.transport.LiveRef liveRef = ((UnicastRef) ref).getLiveRef();
//			return liveRef.getPort();
			
			// load the SUN class if available
			ClassLoader cl = ClassLoader.getSystemClassLoader();
			Class<?> unicastRefClass = cl.loadClass("sun.rmi.server.UnicastRef");

			// get the LiveRef obj
			Method method = unicastRefClass.getMethod(
					"getLiveRef", (Class[]) null);
			Object liveRef = method.invoke(getRef(), (Object[]) null);

			// Load liveref class
			Class<?> liveRefClass = cl.loadClass("sun.rmi.transport.LiveRef");

			// invoke getPort on LiveRef instance
			method = liveRefClass.getMethod(
					"getPort", (Class[]) null);
			return (Integer) method.invoke(liveRef, (Object[]) null);
		} catch (SecurityException e) {
			MP.printError(EC.GENERAL, "trying to get a port for a worker", e); // LL changed call on 7 April 2012
		} catch (IllegalArgumentException e) {
			MP.printError(EC.GENERAL, "trying to get a port for a worker",e);  // LL changed call on 7 April 2012
		} catch (ClassCastException e) {
			MP.printError(EC.GENERAL, "trying to get a port for a worker",e);  // LL changed call on 7 April 2012
		} catch (NoSuchMethodException e) {
			MP.printError(EC.TLC_DISTRIBUTED_VM_VERSION, e);
		} catch (IllegalAccessException e) {
			MP.printError(EC.TLC_DISTRIBUTED_VM_VERSION, e);
		} catch (InvocationTargetException e) {
			MP.printError(EC.TLC_DISTRIBUTED_VM_VERSION, e);
		} catch (ClassNotFoundException e) {
			MP.printError(EC.TLC_DISTRIBUTED_VM_VERSION, e);
		}
		return 0;
	}

	long getLastInvocation() {
		return lastInvocation;
	}
	
	boolean isComputing() {
		return computing;
	}
	
	public static void main(String args[]) {
		ToolIO.out.println("TLC Worker " + TLCGlobals.versionOfTLC);

		// Must have exactly one arg: a hostname (spec is read from the server
		// connecting to).
		if(args.length != 1) {
			printErrorMsg("Error: Missing hostname of the TLC server to be contacted.");
			return;
		}
		final String serverName = args[0];

		try {
			String url = "//" + serverName + ":" + TLCServer.Port
					+ "/TLCServer";
			
			// try to repeatedly connect to the server until it becomes available
			int i = 1;
			TLCServerRMI server = null;
			while(true) {
				try {
					server = (TLCServerRMI) Naming.lookup(url);
					break;
				} catch (ConnectException e) {
					// if the cause if a java.NET.ConnectException the server is
					// simply not ready yet
					final Throwable cause = e.getCause();
					if(cause instanceof java.net.ConnectException) {
						long sleep = (long) Math.sqrt(i);
						ToolIO.out.println("Server " + serverName
								+ " unreachable, sleeping " + sleep
								+ "s for server to come online...");
						Thread.sleep(sleep * 1000);
						i *= 2;
					} else {
						// some other exception occurred which we do not know
						// how to handle
						throw e;
					}
				}
			}

			long irredPoly = server.getIrredPolyForFP();
			FP64.Init(irredPoly);

			// this call has to be made before the first UniqueString gets
			// created! Otherwise workers and server end up creating different
			// unique strings for the same String value.
			UniqueString.setSource((InternRMI)server);

			if (fts == null) {
				fts = new RMIFilenameToStreamResolver();
			}
			fts.setTLCServer(server);
			
			DistApp work = new TLCApp(server.getSpecFileName(),
					server.getConfigFileName(), server.getCheckDeadlock(),
					server.getPreprocess(), fts);

			final IFPSetManager fpSetManager = server.getFPSetManager();
			
			// spawn twice as many worker threads as we have cores unless user
			// explicitly passes thread count
			final int numCores = Integer.getInteger(TLCWorker.class.getName()
					+ ".threadCount", Runtime.getRuntime()
					.availableProcessors());
			
			runnables = new TLCWorkerRunnable[numCores];
			for (int j = 0; j < numCores; j++) {
				runnables[j] = new TLCWorkerRunnable(j, server, fpSetManager, work);
				Thread t = new Thread(runnables[j], TLCServer.THREAD_NAME_PREFIX + String.format("%03d", j));
				t.start();
			}
			
			// schedule a timer to periodically (60s) check server aliveness 
			keepAliveTimer = new Timer("TLCWorker KeepAlive Timer", true);
			keepAliveTimer.schedule(new TLCTimerTask(keepAliveTimer, runnables, url), 10000, TLCTimerTask.PERIOD);
			
			ToolIO.out.println("TLC worker with " + numCores + " threads ready at: "
					+ new Date());
		} catch (Throwable e) {
			// Assert.printStack(e);
			MP.printError(EC.GENERAL, e);
			ToolIO.out.println("Error: Failed to start worker "
					+ " for server " + serverName + ".\n" + e.getMessage());
		}

		ToolIO.out.flush();
	}

	private static void printErrorMsg(String msg) {
		ToolIO.out.println(msg);
		ToolIO.out
				.println("Usage: java " + TLCWorker.class.getName() + " host");
	}

	public static void setFilenameToStreamResolver(RMIFilenameToStreamResolver aFTS) {
		fts  = aFTS;
	}

	/**
	 * Terminates all {@link TLCWorker}s currently running concurrently by
	 * gracefully unregistering with RMI. Additionally it terminates each
	 * keep-alive timer.
	 */
	public static void shutdown() {
		// Exit the keepAliveTimer
		if (keepAliveTimer != null) {
			keepAliveTimer.cancel();
		}
		
		// Exit and unregister all worker threads
		for (int i = 0; i < runnables.length; i++) {
			TLCWorker worker = runnables[i].getTLCWorker();
			try {
				worker.exit();
			} catch (NoSuchObjectException e) {
				// may happen, ignore
			}
		}
		
		fts = null;
		runnables = new TLCWorkerRunnable[0];
	}

	public static class TLCWorkerRunnable implements Runnable {
		private final TLCServerRMI aServer;
		private final IFPSetManager anFpSetManager;
		private final DistApp aWork;
		private TLCWorker worker;
		private final int threadId;

		public TLCWorkerRunnable(int threadId, TLCServerRMI aServer,
				IFPSetManager anFpSetManager, DistApp aWork) {
			this.threadId = threadId;
			this.aServer = aServer;
			this.anFpSetManager = anFpSetManager;
			this.aWork = aWork;
		}
		
		/* (non-Javadoc)
		 * @see java.lang.Runnable#run()
		 */
		public void run() {
			try {
				worker = new TLCWorker(threadId, aWork, anFpSetManager, InetAddress
						.getLocalHost().getCanonicalHostName());
				aServer.registerWorker(worker);
			} catch (RemoteException e) {
				throw new RuntimeException(e);
			} catch (UnknownHostException e) {
				throw new RuntimeException(e);
			} catch (IOException e) {
				throw new RuntimeException(e);
			}
		}
		
		public TLCWorker getTLCWorker() {
			return worker;
		}
	}
	
	public static class Holder implements Comparable<Holder> {

		private final long fp;
		private final TLCState successor;
		private final TLCState predecessor;

		public Holder(long fp, TLCState successor, TLCState predecessor) {
			this.fp = fp;
			this.successor = successor;
			this.predecessor = predecessor;
		}

		/**
		 * @return the fp
		 */
		public long getFp() {
			return fp;
		}

		/**
		 * @return the successor
		 */
		public TLCState getNewState() {
			return successor;
		}

		/**
		 * @return the predecessor
		 */
		public TLCState getParentState() {
			return predecessor;
		}

		/* (non-Javadoc)
		 * @see java.lang.Comparable#compareTo(java.lang.Object)
		 */
		public int compareTo(Holder o) {
			return (fp < o.fp) ? -1 : ((fp == o.fp) ? 0 : 1);
		}
	}
}
