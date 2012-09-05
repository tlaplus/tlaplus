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
import java.util.List;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import tlc2.tool.distributed.fp.callable.CheckFPsCallable;
import tlc2.tool.distributed.fp.callable.ContainsBlockCallable;
import tlc2.tool.distributed.fp.callable.PutBlockCallable;
import tlc2.util.BitVector;
import tlc2.util.LongVec;
import util.ToolIO;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
@SuppressWarnings("serial")
public abstract class FPSetManager implements IFPSetManager {

	protected long mask = 0x7FFFFFFFFFFFFFFFL;
	/**
	 * A list of pairs. A pair is a remote reference and its corresponding
	 * hostname. The name is cached locally to report it correctly in the error
	 * case, where it's impossible to call {@link FPSetRMI#getHostname}.
	 */
	protected List<FPSets> fpSets;

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
		
		// No FPSets left that can be used
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
				System.out.println("Warning: Failed to connect from "
						+ this.getHostName() + " to the fp server at "
						+ this.fpSets.get(fpIdx).getHostname() + ".\n" + e.getMessage());
				e.printStackTrace();
				if (this.reassign(fpIdx) == -1) {
					System.out
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
				System.out.println("Warning: Failed to connect from "
						+ this.getHostName() + " to the fp server at "
						+ this.fpSets.get(fpIdx).getHostname() + ".\n" + e.getMessage());
				e.printStackTrace();
				if (this.reassign(fpIdx) == -1) {
					System.out
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
				System.out.println("Warning: Failed to connect from "
						+ this.getHostName() + " to the fp server at "
						+ this.fpSets.get(i).getHostname() + ".\n" + e.getMessage());
				e.printStackTrace();
				if (this.reassign(i) == -1) {
					System.out
							.println("Warning: there is no fp server available.");
				}
				res[i] = new BitVector(fps[i].size());
				res[i].set(0, fps[i].size() - 1);
			}
		}
		return res;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.IFPSetManager#putBlock(tlc2.util.LongVec[], java.util.concurrent.ExecutorService)
	 */
	public BitVector[] putBlock(final LongVec[] fps, final ExecutorService executorService) {
		final int len = this.fpSets.size();
		
		// Synchronize this and nested threads
		final CountDownLatch cdl = new CountDownLatch(len);
		
		final List<Future<BitVector>> futures = new ArrayList<Future<BitVector>>();
		for (int i = 0; i < len; i++) {
			futures.add(executorService.submit(new PutBlockCallable(this, cdl, fpSets.get(i), fps, i)));
		}
		
		try {
			// Wait for all threads to finish
			cdl.await();
		
			// Convert and return result
			final BitVector[] res = new BitVector[len];
			for (int i = 0; i < res.length; i++) {
					res[i] = futures.get(i).get();
			}
			return res;
		} catch (InterruptedException e) {
			// not expected to happen, fail fast for the moment.
			e.printStackTrace();
			return null;
		} catch (ExecutionException e) {
			// not expected to happen, fail fast for the moment.
			e.printStackTrace();
			return null;
		}
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
				System.out.println("Warning: Failed to connect from "
						+ this.getHostName() + " to the fp server at "
						+ this.fpSets.get(i).getHostname() + ".\n" + e.getMessage());
				e.printStackTrace();
				if (this.reassign(i) == -1) {
					System.out
							.println("Warning: there is no fp server available.");
				}
				res[i] = new BitVector(fps[i].size());
				res[i].set(0, fps[i].size() - 1);
			}
		}
		return res;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.IFPSetManager#containsBlock(tlc2.util.LongVec[], java.util.concurrent.ExecutorService)
	 */
	public BitVector[] containsBlock(final LongVec[] fps, final ExecutorService executorService) {
		final int len = this.fpSets.size();
		
		// Synchronize this and nested threads
		final CountDownLatch cdl = new CountDownLatch(len);
		
		final List<Future<BitVector>> futures = new ArrayList<Future<BitVector>>();
		for (int i = 0; i < len; i++) {
			futures.add(executorService.submit(new ContainsBlockCallable(this, cdl, fpSets.get(i), fps, i)));
		}
		
		try {
			// Wait for all threads to finish
			cdl.await();
			
			// Convert and return result
			final BitVector[] res = new BitVector[len];
			for (int i = 0; i < res.length; i++) {
				res[i] = futures.get(i).get();
			}
			return res;
		} catch (InterruptedException e) {
			// not expected to happen, fail fast for the moment.
			e.printStackTrace();
			return null;
		} catch (ExecutionException e) {
			// not expected to happen, fail fast for the moment.
			e.printStackTrace();
			return null;
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.IFPSetManager#checkFPs()
	 */
	public double checkFPs() {
		final int len = this.fpSets.size();
		
		// Synchronize this and nested threads
		final CountDownLatch cdl = new CountDownLatch(len);
		
		// Instantiation of a thread pool here is fine, as long as checkFPs is only called seldomly.
		final ExecutorService executorService = Executors.newFixedThreadPool(len);
		try {
			// Start checkFP on all FPSets concurrently
			// (checkFPs scans the full set sequentially!)
			final List<Future<Double>> futures = new ArrayList<Future<Double>>();
			for (int i = 0; i < len; i++) {
				futures.add(executorService.submit(new CheckFPsCallable(cdl, fpSets.get(i).getFpset())));
			}

			// Wait for all threads to finish
			cdl.await();
			
			// Return minimum value
			double res = Double.MAX_VALUE;
			for (Future<Double> future : futures) {
				res = Math.min(res, future.get());
			}
			return res;
		} catch (InterruptedException e) {
			// not expected to happen, could return an approximation
			// if happens (but fail fast for the moment).
			e.printStackTrace();
			return -1;
		} catch (ExecutionException e) {
			// not expected to happen, could return an approximation
			// if happens (but fail fast for the moment).
			e.printStackTrace();
			return -1;
		} finally {
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
				System.out.println("Warning: Failed to connect from "
						+ this.getHostName() + " to the fp server at "
						+ this.fpSets.get(i).getHostname() + ".\n" + e.getMessage());
				e.printStackTrace();
				if (this.reassign(i) == -1) {
					System.out
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
		int len = this.fpSets.size();
		long res = 1; // the initial state
		for (int i = 0; i < len; i++) {
			try {
				res += this.fpSets.get(i).getStatesSeen();
			} catch (Exception e) {
				System.out.println("Warning: Failed to connect from "
						+ this.getHostName() + " to the fp server at "
						+ this.fpSets.get(i).getHostname() + ".\n" + e.getMessage());
				e.printStackTrace();
				if (this.reassign(i) == -1) {
					System.out
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
	 * @see tlc2.tool.distributed.fp.IFPSetManager#addThread()
	 */
	public void addThread() throws IOException {
		// no-op, added due to polymorphism with NonDistribuedFPSetManager
		//TODO How do distributed FPSets handle additional readers/writers?
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
