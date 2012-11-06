// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.distributed.fp;

import java.io.IOException;
import java.util.concurrent.ExecutorService;

import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.util.BitVector;
import tlc2.util.LongVec;

@SuppressWarnings("serial")
public class NonDistributedFPSetManager implements IFPSetManager {

	private final FPSetRMI fpSet;
	private final String hostname;

	public NonDistributedFPSetManager(final FPSetRMI fpSet,
			final String hostname) throws IOException {
		this.fpSet = fpSet;
		this.hostname = hostname;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.IFPSetManager#register(tlc2.tool.distributed.fp.FPSetRMI, java.lang.String)
	 */
	public void register(FPSetRMI fpSet, String hostname)
			throws FPSetManagerException {
		throw new UnsupportedOperationException("Not applicable for non-distributed FPSetManager");
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#numOfServers()
	 */
	public int numOfServers() {
		return 1;
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.IFPSetManager#numOfAliveServers()
	 */
	public int numOfAliveServers() {
		return numOfAliveServers();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#getHostName()
	 */
	public String getHostName() {
		return hostname;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#put(long)
	 */
	public boolean put(long fp) {
		try {
			return this.fpSet.put(fp);
		} catch (IOException e) {
			// not expected to happen
			MP.printError(EC.GENERAL, e);
			return false;
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#contains(long)
	 */
	public boolean contains(long fp) {
		try {
			return this.fpSet.contains(fp);
		} catch (IOException e) {
			// not expected to happen
			MP.printError(EC.GENERAL, e);
			return false;
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.IFPSetManager#getFPSetIndex(long)
	 */
	public int getFPSetIndex(long fp) {
		return 0;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#putBlock(tlc2.util.LongVec[])
	 */
	public BitVector[] putBlock(LongVec[] fps) {
		final BitVector[] res = new BitVector[fps.length];
		for (int i = 0; i < fps.length; i++) {
			LongVec longVec = fps[i];
			try {
				res[i] = this.fpSet.putBlock(longVec);
			} catch (IOException e) {
				// not expected to happen
				MP.printError(EC.GENERAL, e);
				res[i] = new BitVector(0);
			}
		}
		return res;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#putBlock(tlc2.util.LongVec[], java.util.concurrent.ExecutorService)
	 */
	public BitVector[] putBlock(LongVec[] fps, ExecutorService executorService) {
		return putBlock(fps);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#containsBlock(tlc2.util.LongVec[])
	 */
	public BitVector[] containsBlock(LongVec[] fps) {
		final BitVector[] res = new BitVector[fps.length];
		for (int i = 0; i < fps.length; i++) {
			LongVec longVec = fps[i];
			try {
				res[i] = this.fpSet.containsBlock(longVec);
			} catch (IOException e) {
				// not expected to happen
				MP.printError(EC.GENERAL, e);
				res[i] = new BitVector(0);
			}
		}
		return res;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#containsBlock(tlc2.util.LongVec[], java.util.concurrent.ExecutorService)
	 */
	public BitVector[] containsBlock(LongVec[] fps,
			ExecutorService executorService) {
		return containsBlock(fps);
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#checkFPs()
	 */
	public double checkFPs() {
		try {
			return this.fpSet.checkFPs();
		} catch (IOException e) {
			// not expected to happen
			MP.printError(EC.GENERAL, e);
			return -1;
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#size()
	 */
	public long size() {
		try {
			return this.fpSet.size();
		} catch (IOException e) {
			// not supposed to happen
			MP.printError(EC.GENERAL, e);
			return -1;
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#getStatesSeen()
	 */
	public long getStatesSeen() {
		try {
			return this.fpSet.size();
		} catch (IOException e) {
			// not supposed to happen
			MP.printError(EC.GENERAL, e);
			return -1;
		}
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#getMask()
	 */
	public long getMask() {
		return Long.MAX_VALUE;
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#checkpoint(java.lang.String)
	 */
	public void checkpoint(String fname) throws InterruptedException, IOException {
		this.fpSet.beginChkpt();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.IFPSetManager#commitChkpt()
	 */
	public void commitChkpt() throws IOException {
		this.fpSet.commitChkpt();
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#recover(java.lang.String)
	 */
	public void recover(String fname) throws InterruptedException, IOException {
		this.fpSet.recover();
	}

	/* (non-Javadoc)
	 * @see tlc2.tool.distributed.fp.FPSetManager#close(boolean)
	 */
	public void close(boolean cleanup) throws IOException {
		this.fpSet.close();
		// Correspond with the existing impl in FPSetManager#exit(boolean) and
		// exit the FPSet
		this.fpSet.exit(cleanup);
	}
}
