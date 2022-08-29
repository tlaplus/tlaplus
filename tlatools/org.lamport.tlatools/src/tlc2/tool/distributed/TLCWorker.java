// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:18:40 PST by lamport  
//      modified on Thu May 31 13:24:56 PDT 2001 by yuanyu   

package tlc2.tool.distributed;

import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.TLCState;
import tlc2.tool.WorkerException;
import tlc2.tool.distributed.fp.IFPSetManager;
import tlc2.util.Cache;
import tlc2.util.FP64;
import tlc2.util.LongVec;
import tlc2.util.SimpleCache;
import util.Assert;
import util.ToolIO;
import util.UniqueString;

import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.InetAddress;
import java.net.URI;
import java.rmi.*;
import java.rmi.server.UnicastRemoteObject;
import java.util.*;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.RejectedExecutionException;

@SuppressWarnings("serial")
public class TLCWorker extends UnicastRemoteObject implements TLCWorkerRMI {

    private static final boolean unsorted = Boolean.getBoolean(TLCWorker.class.getName() + ".unsorted");
    private static final ExecutorService executorService = Executors.newCachedThreadPool();
    private static Timer keepAliveTimer;
    private static RMIFilenameToStreamResolver fts;
    private static TLCWorkerRunnable[] runnables = new TLCWorkerRunnable[0];

    private static volatile CountDownLatch cdl;

    private final DistApp work;
    private final IFPSetManager fpSetManager;
    private final URI uri;
    private final Cache cache;
    /**
     * Indicate whether the worker is busy computing states
     */
    private volatile boolean computing = false;
    private long lastInvocation;
    private long overallStatesComputed;


    public TLCWorker(final int threadId, final DistApp work, final IFPSetManager fpSetManager, final String aHostname)
            throws RemoteException {
        this.work = work;
        this.fpSetManager = fpSetManager;
        this.uri = URI.create("rmi://" + aHostname + ":" + getPort() + "/"
                + threadId);

        this.cache = new SimpleCache();
    }

    public static void main(final String[] args) {
        ToolIO.out.println("TLC Worker " + TLCGlobals.versionOfTLC);

        // Must have exactly one arg: a hostname (spec is read from the server
        // connecting to).
        if (args.length != 1) {
            printErrorMsg("Error: Missing hostname of the TLC server to be contacted.");
            return;
        }
        final String serverName = args[0];

        // spawn as many worker threads as we have cores unless user
        // explicitly passes thread count
        final int numCores = Integer.getInteger(TLCWorker.class.getName()
                + ".threadCount", Runtime.getRuntime()
                .availableProcessors());

        cdl = new CountDownLatch(numCores);

        try {
            final String url = "//" + serverName + ":" + TLCServer.Port
                    + "/" + TLCServer.SERVER_WORKER_NAME;

            // try to repeatedly connect to the server until it becomes available
            int i = 1;
            TLCServerRMI server = null;
            while (!Thread.currentThread().isInterrupted()) {
                try {
                    server = (TLCServerRMI) Naming.lookup(url);
                    break;
                } catch (final ConnectException e) {
                    // if the cause is a java.NET.ConnectException the server is
                    // simply not ready yet
                    final Throwable cause = e.getCause();
                    if (cause instanceof java.net.ConnectException) {
                        final long sleep = (long) Math.sqrt(i);
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
                } catch (final NotBoundException e) {
                    // Registry is available but no object by "TLCServer". This
                    // happens when TLCServer makes it registry available but
                    // has't registered itself yet.
                    final long sleep = (long) Math.sqrt(i);
                    ToolIO.out.println("Server " + serverName + " reachable but not ready yet, sleeping " + sleep
                            + "s for server to come online...");
                    Thread.sleep(sleep * 1000);
                    i *= 2;
                }
                // It is vital to *not* catch NoRouteToHostException or
                // UnknownHostException. TLCWorker is supposed to terminate when
                // either of the two is thrown. The rational is that the while
                // loop could be going while TLCServer is busy generating a huge
                // set of init states. Close to completion, it finds a violating
                // state and terminates. In case of cloud distributed TLC
                // (see CloudDistributedTLCJob), the host/vm running the master
                // immediately shuts down. That is when the NoRouteToHostException
                // will make sure that the set of TLCWorkers will terminate the VM
                // and shutdown the vm too. There is obviously the chance that
                // another vm gets the IP of the former master assigned and boots
                // up during a sleep period above. Even though I do not know what
                // holding period IP address have across the various cloud providers,
                // I find this rather unlikely.
            }

            final long irredPoly = Objects.requireNonNull(server).getIrredPolyForFP();
            FP64.Init(irredPoly);

            // this call has to be made before the first UniqueString gets
            // created! Otherwise workers and server end up creating different
            // unique strings for the same String value.
            UniqueString.setSource((InternRMI) server);

            if (fts == null) {
                fts = new RMIFilenameToStreamResolver();
            }
            fts.setTLCServer(server);

            final DistApp work = new TLCApp(server.getSpecFileName(),
                    server.getConfigFileName(), server.getCheckDeadlock(), fts);

            final IFPSetManager fpSetManager = server.getFPSetManager();

            runnables = new TLCWorkerRunnable[numCores];
            for (int j = 0; j < numCores; j++) {
                runnables[j] = new TLCWorkerRunnable(j, server, fpSetManager, work);
                final Thread t = new Thread(runnables[j], TLCServer.THREAD_NAME_PREFIX + String.format("%03d", j));
                t.start();
            }

            // schedule a timer to periodically (60s) check server aliveness
            keepAliveTimer = new Timer("TLCWorker KeepAlive Timer", true);
            keepAliveTimer.schedule(new TLCTimerTask(keepAliveTimer, runnables, url), 10000, TLCTimerTask.PERIOD);

            ToolIO.out.println("TLC worker with " + numCores + " threads ready at: "
                    + new Date());
        } catch (final Throwable e) {
            // Assert.printStack(e);
            MP.printError(EC.GENERAL, e);
            ToolIO.out.println("Error: Failed to start worker "
                    + " for server " + serverName + ".\n" + e.getMessage());
        }

        ToolIO.out.flush();
    }

    private static void printErrorMsg(final String msg) {
        ToolIO.out.println(msg);
        ToolIO.out
                .println("Usage: java " + TLCWorker.class.getName() + " host");
    }

    public static void setFilenameToStreamResolver(final RMIFilenameToStreamResolver aFTS) {
        fts = aFTS;
    }

    /**
     * Terminates all {@link TLCWorker}s currently running concurrently by
     * gracefully unregistering with RMI. Additionally it terminates each
     * keep-alive timer.
     */
    public static void shutdown() throws Exception {
        // Exit the keepAliveTimer
        if (keepAliveTimer != null) {
            keepAliveTimer.cancel();
        }

        // Exit and unregister all worker threads
        for (final TLCWorkerRunnable runnable : runnables) {
            final TLCWorker worker = runnable.getTLCWorker();
            try {
                if (worker != null) {
                    worker.close();
                }
            } catch (final NoSuchObjectException e) {
                // may happen, ignore
            }
        }

        fts = null;
        runnables = new TLCWorkerRunnable[0];
    }

    public static void awaitTermination() throws InterruptedException {
        cdl.await();

        // Sleep 10 seconds for TLCServer to dispose itself. Otherwise
        // if callees wait for this termination, they might end up connecting to
        // the old TLCServer instance once
        // _again_.
        Thread.sleep(10L * 1000);
    }

    //TODO Remove once performance tests show superiority of TreeSet
    private Set<Holder> getSet() {
        if (unsorted) {
            return new HashSet<>();
        } else {
            return new TreeSet<>();
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.TLCWorkerRMI#getNextStates(tlc2.tool.TLCState[])
     */
    @SuppressWarnings("unchecked")
    @Override
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
            for (final TLCState state : states) {
                state1 = state;
                nstates = this.work.getNextStates(state1);
                // Keep statistics about states computed during this invocation
                statesComputed += nstates.length;
                // add all succ states/fps to the array designated for the corresponding fp server
                for (final TLCState nstate : nstates) {
                    final long fp = nstate.fingerPrint();
                    if (!cache.hit(fp)) {
                        treeSet.add(new Holder(fp, nstate, state1));
                    }
                }
            }

            // Amount of states computed in during all invocations
            overallStatesComputed += statesComputed;

            // create containers for each fingerprint _server_
            final int fpServerCnt = this.fpSetManager.numOfServers();
            // previous state
            final ArrayList<TLCState>[] pvv = new ArrayList[fpServerCnt];
            // container for all succ states
            final ArrayList<TLCState>[] nvv = new ArrayList[fpServerCnt];
            // container for all succ state fingerprints
            final LongVec[] fpvv = new LongVec[fpServerCnt];
            for (int i = 0; i < fpServerCnt; i++) {
                pvv[i] = new ArrayList<>();
                nvv[i] = new ArrayList<>();
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
                final long fp = holder.getFp();
                Assert.check(last < fp, EC.GENERAL);
                last = fp;

                final int fpIndex = fpSetManager.getFPSetIndex(fp);
                pvv[fpIndex].add(holder.getParentState());
                nvv[fpIndex].add(holder.getNewState());
                fpvv[fpIndex].add(fp);
            }

            final BitSet[] visited = this.fpSetManager.containsBlock(fpvv, executorService);

            // Remove the states that have already been seen, check if the
            // remaining new states are valid and inModel.
            final ArrayList<TLCState>[] newStates = new ArrayList[fpServerCnt];
            final LongVec[] newFps = new LongVec[fpServerCnt];
            for (int i = 0; i < fpServerCnt; i++) {
                newStates[i] = new ArrayList<>();
                newFps[i] = new LongVec();
            }

            for (int i = 0; i < fpServerCnt; i++) {
                for (var it = visited[i].stream().iterator(); it.hasNext(); ) {
                    var index = it.next();
                    state1 = pvv[i].get(index);
                    state2 = nvv[i].get(index);
                    this.work.checkState(state1, state2);
                    if (this.work.isInModel(state2)
                            && this.work.isInActions(state1, state2)) {
                        state2.uid = state1.uid;
                        newStates[i].add(state2);
                        newFps[i].add(fpvv[i].get(index));
                    }
                }
            }

            // Prepare the return value.
            final long computationTime = System.currentTimeMillis() - lastInvocation;
            return new NextStateResult(newStates, newFps, computationTime, statesComputed);
        } catch (final WorkerException e) {
            throw e;
        } catch (final OutOfMemoryError e) {
            throw new RemoteException("OutOfMemoryError occurred at worker: " + uri.toASCIIString(), e);
        } catch (final RejectedExecutionException e) {
            throw new RemoteException("Executor rejected task at worker: " + uri.toASCIIString(), e);
        } catch (final Throwable e) {
            throw new WorkerException(e.getMessage(), e, state1, state2, true);
        } finally {
            computing = false;
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.TLCWorkerRMI#exit()
     */
    @Override
    public void close() throws Exception {
        ToolIO.out.println(uri.getHost() + ", work completed at: " + new Date() + " Computed: "
                + overallStatesComputed
                + " and a cache hit ratio of " + this.cache.getHitRatioAsString()
                + ", Thank you!");

        executorService.shutdown();

        keepAliveTimer.cancel();

        UnicastRemoteObject.unexportObject(TLCWorker.this, true);

        cdl.countDown();
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.TLCWorkerRMI#isAlive()
     */
    @Override
    public boolean isAlive() {
        return true;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.TLCWorkerRMI#getURI()
     */
    @Override
    public URI getURI() throws RemoteException {
        return uri;
    }

    /* (non-Javadoc)
     * @see tlc2.tool.distributed.TLCWorkerRMI#getCacheRateRatio()
     */
    @Override
    public double getCacheRateRatio() throws RemoteException {
        return this.cache.getHitRatio();
    }

    private int getPort() {
        try {
            // this only works on >= Sun Java 1.6
//			sun.rmi.transport.LiveRef liveRef = ((UnicastRef) ref).getLiveRef();
//			return liveRef.getPort();

            // load the SUN class if available
            final ClassLoader cl = ClassLoader.getSystemClassLoader();
            final Class<?> unicastRefClass = cl.loadClass("sun.rmi.server.UnicastRef");

            // get the LiveRef obj
            Method method = unicastRefClass.getMethod(
                    "getLiveRef", (Class[]) null);
            final Object liveRef = method.invoke(getRef(), (Object[]) null);

            // Load liveref class
            final Class<?> liveRefClass = cl.loadClass("sun.rmi.transport.LiveRef");

            // invoke getPort on LiveRef instance
            method = liveRefClass.getMethod(
                    "getPort", (Class[]) null);
            return (Integer) method.invoke(liveRef, (Object[]) null);
        } catch (final SecurityException | ClassCastException | IllegalArgumentException e) {
            MP.printError(EC.GENERAL, "trying to get a port for a worker", e); // LL changed call on 7 April 2012
        } catch (final NoSuchMethodException | ClassNotFoundException | InvocationTargetException |
                       IllegalAccessException e) {
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

    public static class TLCWorkerRunnable implements Runnable {
        private final TLCServerRMI aServer;
        private final IFPSetManager anFpSetManager;
        private final DistApp aWork;
        private final int threadId;
        private TLCWorker worker;

        public TLCWorkerRunnable(final int threadId, final TLCServerRMI aServer,
                                 final IFPSetManager anFpSetManager, final DistApp aWork) {
            this.threadId = threadId;
            this.aServer = aServer;
            this.anFpSetManager = anFpSetManager;
            this.aWork = aWork;
        }

        /* (non-Javadoc)
         * @see java.lang.Runnable#run()
         */
        @Override
        public void run() {
            try {
                worker = new TLCWorker(threadId, aWork, anFpSetManager, InetAddress
                        .getLocalHost().getCanonicalHostName());
                aServer.registerWorker(worker);
            } catch (final IOException e) {
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

        public Holder(final long fp, final TLCState successor, final TLCState predecessor) {
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
        @Override
        public int compareTo(final Holder o) {
            return Long.compare(fp, o.fp);
        }
    }
}
