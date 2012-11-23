// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:13:43 PST by lamport
//      modified on Wed Jan 10 00:09:44 PST 2001 by yuanyu

package tlc2.tool.distributed.fp;

import java.io.IOException;
import java.io.Serializable;
import java.net.InetAddress;
import java.rmi.RemoteException;
import java.rmi.UnmarshalException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.RejectedExecutionException;
import java.util.logging.Level;
import java.util.logging.Logger;

import tlc2.output.EC;
import tlc2.tool.distributed.fp.callable.BitVectorWrapper;
import tlc2.tool.distributed.fp.callable.CheckFPsCallable;
import tlc2.tool.distributed.fp.callable.ContainsBlockCallable;
import tlc2.tool.distributed.fp.callable.PutBlockCallable;
import tlc2.util.BitVector;
import tlc2.util.LongVec;
import util.Assert;
import util.ToolIO;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
@SuppressWarnings("serial")
public abstract class FPSetManager implements IFPSetManager {
	
	private static final Random rnd = new Random();
	
	private final static Logger LOGGER = Logger.getLogger(FPSetManager.class.getName());

	protected long mask = 0x7FFFFFFFFFFFFFFFL;
	/**
	 * A list of pairs. A pair is a remote reference and its corresponding
	 * hostname. The name is cached locally to report it correctly in the error
	 * case, where it's impossible to call {@link FPSetRMI#getHostname}.
	 */
	protected List<FPSets> fpSets;
	
	protected boolean managerIsBroken = false; 

	// SZ Jul 13, 2009: moved from FPSetRMI
	public static int Port = 10998; // port # for fpset server

	public FPSetManager() {
		 this(new ArrayList<FPSets>());
	}
	
	public FPSetManager(List<FPSets> fpSets) {
		this.fpSets = fpSets;
	}

	public FPSetManager(FPSetRMI fpSet) {
		this();
		this.fpSets.add(new FPSets(fpSet, fpSet.toString()));
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#numOfServers()
	 */
	public int numOfServers() {
		return this.fpSets.size();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.IFPSetManager#numOfAliveServers()
	 */
	public int numOfAliveServers() {
		// Add all fpsets to a set to remove the duplicates. The duplicates stem
		// from reassigning alive fpsets to the slot of a dead one.
		final Set<FPSets> s = new HashSet<FPSets>();
		s.addAll(this.fpSets);
		
		int aliveServer = 0;

		final Iterator<FPSets> itr = s.iterator();
		while (itr.hasNext()) {
			if (itr.next().isAvailable()) {
				aliveServer++;
			}
		}
		return aliveServer;
	}

	/**
	 * Replace the FPSet at the given index from the list of FPSets with the
	 * next available successor in the list.
	 * 
	 * @param index Corresponds to the FPSet to be replaced
	 * @return The index of the replacement or <code>-1</code> if no functional FPSet left.
	 */
	public synchronized int reassign(final int index) {
		// Guard against invalid indices
		if (index < 0 || index >= this.fpSets.size()) {
			throw new IllegalArgumentException("index not within bounds");
		}
		
		// Avoid cycling over the list of broken FPSets if all are broken
		// anyway. This is just a performance enhancement in that it prevents
		// the code from looping over the (potentially large) list of nested
		// FPSets.
		// Since the method is synchronized, we do not need to guard
		// managerIsBroken from concurrent access.
		if (managerIsBroken) {
			return -1;
		}
		
		// The broken FPSet
		final FPSets broken = this.fpSets.get(index);
		broken.setUnavailable();

		// Calculate the index of the successor
		int next = (index + 1) % this.fpSets.size();
		
		// Loop until we wrap around which would indicate that no functional
		// FPsets are left
		while (next != index) {
			final FPSets replacement = this.fpSets.get(next);
			if (replacement.isAvailable()) {
				for (int j = index; j < next; j++) {
					this.fpSets.set(j, replacement);
				}
				return next;
			}
			next = (next + 1) % this.fpSets.size();
		}
		
		// No FPSets left that can be used.
		// Mark the FPSetManager itself as broken and cache it for subsequent
		// calls.
		managerIsBroken = true;
		
		return -1;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#close(boolean)
	 */
	public void close(boolean cleanup) throws IOException {
		FPSets curr = null;
		int len = this.fpSets.size();
		int idx = 0, lidx = 0;

		for (idx = 0; idx < len; idx++) {
			curr = this.fpSets.get(idx);
			if (curr != null)
				break;
		}
		if (curr == null)
			return;

		for (lidx = len - 1; lidx > idx; lidx--) {
			FPSets last = this.fpSets.get(lidx);
			if (last != null && last != curr)
				break;
		}
		for (int i = idx + 1; i <= lidx; i++) {
			FPSets next = this.fpSets.get(i);
			if (next != null && next != curr) {
				try {
					curr.exit(cleanup);
				} catch (UnmarshalException e) {
					// happens when the DiskFPSet closes it calls System.exit
				} catch (Exception e) {
					e.printStackTrace();
				}
				curr = next;
			}
		}
		if (curr != null) {
			try {
				curr.exit(cleanup);
			} catch (UnmarshalException e) {
				// happens when the DiskFPSet closes it calls System.exit
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

	public String getHostName() {
		String hostname = "Unknown";
		try {
			hostname = InetAddress.getLocalHost().getHostName();
		} catch (Exception e) {
			e.printStackTrace();
		}
		return hostname;
	}

	protected int getIndex(long fp) {
		long l = fp & mask;
		return (int) (l % this.fpSets.size());
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#put(long)
	 */
	public boolean put(long fp) {
		int fpIdx = getIndex(fp);
		while (true) {
			try {
				return this.fpSets.get(fpIdx).put(fp);
			} catch (Exception e) {
				ToolIO.out.println("Warning: Failed to connect from "
						+ this.getHostName() + " to the fp server at "
						+ this.fpSets.get(fpIdx).getHostname() + ".\n" + e.getMessage());
				if (this.reassign(fpIdx) == -1) {
					ToolIO.out
							.println("Warning: there is no fp server available.");
					return false;
				}
			}
		}
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#contains(long)
	 */
	public boolean contains(long fp) {
		int fpIdx = getIndex(fp);
		while (true) {
			try {
				return this.fpSets.get(fpIdx).contains(fp);
			} catch (Exception e) {
				ToolIO.out.println("Warning: Failed to connect from "
						+ this.getHostName() + " to the fp server at "
						+ this.fpSets.get(fpIdx).getHostname() + ".\n" + e.getMessage());
				if (this.reassign(fpIdx) == -1) {
					ToolIO.out
							.println("Warning: there is no fp server available.");
					return false;
				}
			}
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.IFPSetManager#getFPSetIndex(long)
	 */
	public int getFPSetIndex(long fp) {
		return (int) ((fp & mask) % numOfServers());
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#putBlock(tlc2.util.LongVec[])
	 */
	public BitVector[] putBlock(LongVec[] fps) {
		int len = this.fpSets.size();
		BitVector[] res = new BitVector[len];
		for (int i = 0; i < len; i++) {
			try {
				res[i] = this.fpSets.get(i).putBlock(fps[i]);
			} catch (Exception e) {
				ToolIO.out.println("Warning: Failed to connect from "
						+ this.getHostName() + " to the fp server at "
						+ this.fpSets.get(i).getHostname() + ".\n" + e.getMessage());
				if (this.reassign(i) == -1) {
					ToolIO.out
							.println("Warning: there is no fp server available.");
					// Indicate for all fingerprints of the lost fpset that they are
					// new. This is achieved by setting all bits in BitVector.
					res[i] = new BitVector(fps[i].size(), true);
				} else {
					// Cause for loop to retry the current fps[i] to the newly
					// assigned fingerprint set
					i -= 1;
				}
			}
		}
		return res;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.IFPSetManager#putBlock(tlc2.util.LongVec[], java.util.concurrent.ExecutorService)
	 */
	public BitVector[] putBlock(final LongVec[] fps, final ExecutorService executorService) {
		// Create a Callable for each fingerprint set
		final int len = this.fpSets.size();
		final List<Callable<BitVectorWrapper>> solvers = new ArrayList<Callable<BitVectorWrapper>>();
		for (int i = 0; i < len; i++) {
			solvers.add(new PutBlockCallable(this, fpSets, fps, i));
		}

		return executeCallablesAndCollect(executorService, solvers);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#containsBlock(tlc2.util.LongVec[])
	 */
	public BitVector[] containsBlock(LongVec[] fps) {
		int len = this.fpSets.size();
		BitVector[] res = new BitVector[len];
		for (int i = 0; i < len; i++) {
			try {
				res[i] = this.fpSets.get(i).containsBlock(fps[i]);
			} catch (Exception e) {
				ToolIO.out.println("Warning: Failed to connect from "
						+ this.getHostName() + " to the fp server at "
						+ this.fpSets.get(i).getHostname() + ".\n" + e.getMessage());
				if (this.reassign(i) == -1) {
					ToolIO.out
							.println("Warning: there is no fp server available.");
					// Indicate for all fingerprints of the lost fpset that they are
					// new. This is achieved by setting all bits in BitVector.
					res[i] = new BitVector(fps[i].size(), true);
				} else {
					// Cause for loop to retry the current fps[i] to the newly
					// assigned fingerprint set
					i -= 1;
				}
			}
		}
		return res;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.IFPSetManager#containsBlock(tlc2.util.LongVec[], java.util.concurrent.ExecutorService)
	 */
	public BitVector[] containsBlock(final LongVec[] fps, final ExecutorService executorService) {
		// Create a Callable for each fingerprint set
		final int len = this.fpSets.size();
		final List<Callable<BitVectorWrapper>> solvers = new ArrayList<Callable<BitVectorWrapper>>();
		for (int i = 0; i < len; i++) {
			solvers.add(new ContainsBlockCallable(this, fpSets, fps, i));
		}

		return executeCallablesAndCollect(executorService, solvers);
	}

	/**
	 * Executes the given solvers by using the executor service. Afterwards it
	 * waits for completion and collects the results.
	 */
	private BitVector[] executeCallablesAndCollect(final ExecutorService executorService, 
			final List<Callable<BitVectorWrapper>> solvers) {
		// Have the callables executed by the executor service
		int retry = 0;
		final CompletionService<BitVectorWrapper> ecs = new ExecutorCompletionService<BitVectorWrapper>(executorService);
		for (int i = 0; i < solvers.size(); i++) {
			final Callable<BitVectorWrapper> s = solvers.get(i);
			try {
				ecs.submit(s);
				// reset retry after successfully scheduling a callable
				retry = 0;
			} catch (RejectedExecutionException e) {
				// Throttle current execution if executor service is rejecting
				// task due to excessive task submission
				if (retry++ < 3 && !executorService.isShutdown()) {
					// Determine sleep interval [1,5] randomly to prevent all waiters
					// from retrying at the same moment.
					int sleep = 1 + rnd.nextInt(5);
					
					LOGGER.log(
							Level.FINE,
							"{0}. time throttleing task submission due to overload during FPSetManager callable execution #{1} for {2} seconds",
							new Object[] {retry, i});

					// Sleep for n seconds
					try {
						Thread.sleep(sleep * 1000L);
					} catch (InterruptedException e1) {
						// not expected to happen
						e1.printStackTrace();
					}
					
					// rewind for loop by one to have it schedule the same
					// callable again
					i -= 1;
					continue;
				} else {
					// If ExecutorService has been shut down or REE has been
					// caused for some other reason, re-throw to escalate to
					// higher level exception handling.
					throw e;
				}
			}
		}

		// Wait for completion of the executor service and convert and return
		// result
		final BitVector[] res = new BitVector[solvers.size()];
		for (int i = 0; i < res.length; i++) {
			try {
				// Callers of putBlock and containBlock expect as a post-condition:
				// for all i BitVector[i] is result of LongVec[i].
				// (The LongVec[] order has to reflect itself in the BitVector[] order)
				// Otherwise one is going to see NPEs on the caller end.
				// Thus this code uses a BitVectorWrapper which associates the
				// BitVector return with its LongVec[i] input value.
				final BitVectorWrapper indexBitVector = ecs.take().get();
				final int index = indexBitVector.getIndex();
				// Only one result for a given LongVec[i] is correct
				Assert.check(res[index] == null, EC.GENERAL);
				res[index] = indexBitVector.getBitVector();
			} catch (InterruptedException e) {
				// not expected to happen
				e.printStackTrace();
			} catch (ExecutionException e) {
				// not expected to happen
				e.printStackTrace();
			}
		}
		return res;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#checkFPs()
	 */
	public double checkFPs() {
		final int len = this.fpSets.size();
		// Instantiation of a thread pool here is fine, as long as checkFPs is only called seldomly.
		final ExecutorService executorService = Executors.newFixedThreadPool(len);
		try {
			// Start checkFP on all FPSets concurrently
			// (checkFPs scans the full set sequentially!)
			final CompletionService<Double> ecs = new ExecutorCompletionService<Double>(executorService);
			for (int i = 0; i < len; i++) {
				ecs.submit(new CheckFPsCallable(fpSets.get(i).getFpset()));
			}
			// Return minimum value
			double res = Double.MAX_VALUE;
			for (int i = 0; i < len; i++) {
				try {
					res = Math.min(res, ecs.take().get());
				} catch (InterruptedException e) {
					// not expected to happen, could return an approximation
					// if happens (but fail fast for the moment).
					e.printStackTrace();
				} catch (ExecutionException e) {
					// not expected to happen, could return an approximation
					// if happens (but fail fast for the moment).
					e.printStackTrace();
				}
			}
			return res;
		} finally {
			// Always shutdown the executor service
			executorService.shutdown();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#size()
	 */
	public long size() {
		int len = this.fpSets.size();
		long res = 0;
		for (int i = 0; i < len; i++) {
			try {
				res += this.fpSets.get(i).size();
			} catch (Exception e) {
				ToolIO.out.println("Warning: Failed to connect from "
						+ this.getHostName() + " to the fp server at "
						+ this.fpSets.get(i).getHostname() + ".\n" + e.getMessage());
				if (this.reassign(i) == -1) {
					ToolIO.out
							.println("Warning: there is no fp server available.");
				}
			}
		}
		return res;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#getStatesSeen()
	 */
	public long getStatesSeen() {
		long res = 1; // the initial state
		
		int len = this.fpSets.size();
		for (int i = 0; i < len; i++) {
			try {
				res += this.fpSets.get(i).getStatesSeen();
			} catch (Exception e) {
				ToolIO.out.println("Warning: Failed to connect from "
						+ this.getHostName() + " to the fp server at "
						+ this.fpSets.get(i).getHostname() + ".\n" + e.getMessage());
				if (this.reassign(i) == -1) {
					ToolIO.out
							.println("Warning: there is no fp server available.");
				}
			}
		}
		return res;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#getMask()
	 */
	public long getMask() {
		return mask;
	}

	private final void chkptInner(String fname, boolean chkpt)
			throws InterruptedException {
		int len = this.fpSets.size();
		Checkpoint[] chkpts = new Checkpoint[len];
		FPSets curr = null;
		int cnt = 0, idx = 0, lidx = 0;

		for (idx = 0; idx < len; idx++) {
			curr = this.fpSets.get(idx);
			if (curr != null) {
				chkpts[cnt] = new Checkpoint(idx, fname, chkpt);
				chkpts[cnt].run();
				cnt++;
				break;
			}
		}
		if (curr == null)
			return;

		for (lidx = len - 1; lidx > idx; lidx--) {
			FPSets last = this.fpSets.get(lidx);
			if (last != null && last != curr)
				break;
		}

		for (int i = idx + 1; i <= lidx; i++) {
			FPSets next = this.fpSets.get(i);
			if (next != null && next != curr) {
				curr = next;
				chkpts[cnt] = new Checkpoint(i, fname, chkpt);
				chkpts[cnt].run();
				cnt++;
			}
		}

		for (int i = 0; i < cnt; i++) {
			chkpts[i].join();
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#checkpoint(java.lang.String)
	 */
	public void checkpoint(String fname) throws InterruptedException, IOException {
		chkptInner(fname, true);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.IFPSetManager#commitChkpt()
	 */
	public void commitChkpt() throws IOException {
		// no-op, added due to polymorphism with NonDistribuedFPSetManager
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#recover(java.lang.String)
	 */
	public void recover(String fname) throws InterruptedException, IOException {
		chkptInner(fname, false);
	}

	final class Checkpoint extends Thread {
		int hostIndex;
		String filename;
		boolean isChkpt;

		public Checkpoint(int index, String fname, boolean chkpt) {
			this.hostIndex = index;
			this.filename = fname;
			this.isChkpt = chkpt;
		}

		public void run() {
			try {
				if (this.isChkpt) {
					fpSets.get(this.hostIndex).beginChkpt(this.filename);
					fpSets.get(this.hostIndex).commitChkpt(this.filename);
				} else {
					fpSets.get(this.hostIndex).recover(this.filename);
				}
			} catch (IOException e) {
				ToolIO.out
						.println("Error: Failed to checkpoint the fingerprint server at "
								+ fpSets.get(this.hostIndex).getHostname()
								+ ". This server might be down.");
			}
		}
	}
	
	public static class FPSets implements Serializable {
		private final String hostname;
		private final FPSetRMI fpset;
		/**
		 * Indicates that this FPSetRMI is unavailable (e.g. the node crashed)
		 * and cannot be used anymore.
		 */
		private boolean isAvailable = true;

		public FPSets(FPSetRMI fpset, String hostname) {
			this.fpset = fpset;
			this.hostname = hostname;
		}

		public void setUnavailable() {
			isAvailable = false;
		}
		
		public boolean isAvailable() {
			return isAvailable;
		}

		public void exit(boolean cleanup) throws IOException {
			fpset.exit(cleanup);
		}

		public void recover(String filename) throws IOException {
			fpset.recover(filename);
		}

		public void commitChkpt(String filename) throws IOException {
			fpset.commitChkpt(filename);
		}

		public void beginChkpt(String filename) throws IOException {
			fpset.beginChkpt(filename);
		}

		public long getStatesSeen() throws RemoteException {
			return fpset.getStatesSeen();
		}

		public long size() throws IOException {
			return fpset.size();
		}

		public BitVector containsBlock(LongVec longVec) throws IOException {
			return fpset.containsBlock(longVec);
		}

		public BitVector putBlock(LongVec longVec) throws IOException {
			return fpset.putBlock(longVec);
		}

		public boolean put(long fp) throws IOException {
			return fpset.put(fp);
		}

		public boolean contains(long fp) throws IOException {
			return fpset.contains(fp);
		}
		
		public String getHostname() {
			return hostname;
		}

		public FPSetRMI getFpset() {
			return fpset;
		}
	}
}
