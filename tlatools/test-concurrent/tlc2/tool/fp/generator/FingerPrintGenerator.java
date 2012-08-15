// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp.generator;

import java.io.IOException;
import java.util.Random;
import java.util.concurrent.CountDownLatch;

import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.MultiThreadedFPSetTest;

public class FingerPrintGenerator implements Runnable {

	protected final long insertions;
	protected final Random rnd;
	protected final FPSet fpSet;
	protected final CountDownLatch latch;
	protected final int id;
	protected final MultiThreadedFPSetTest test;
	protected long puts = 0L;
	protected long collisions = 0L;

	public FingerPrintGenerator(MultiThreadedFPSetTest test, int id, FPSet fpSet, CountDownLatch latch, long seed, long insertions) {
		this.test = test;
		this.id = id;
		this.fpSet = fpSet;
		this.latch = latch;
		this.rnd = new Random(seed);
		this.insertions = insertions;
	}

	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		long predecessor = 0L;
		while (fpSet.size() < insertions) {
			try {
				// make sure set still contains predecessor
				if (predecessor != 0L) {
					MultiThreadedFPSetTest.assertTrue(fpSet.contains(predecessor));
				}

				predecessor = rnd.nextLong();

				boolean put = fpSet.put(predecessor);
				if (put == false) {
					puts++;
				} else {
					collisions++;
				}

				// First producer prints stats
				if (id == 0) {
					test.printInsertionSpeed(fpSet.size());
				}

			} catch (IOException e) {
				e.printStackTrace();
				MultiThreadedFPSetTest.fail("Unexpected");
			}
		}
		latch.countDown();
	}

	public int getId() {
		return id;
	}

	/**
	 * @return the puts
	 */
	public long getPuts() {
		return puts;
	}

	/**
	 * @return the collisions
	 */
	public long getCollisions() {
		return collisions == 0 ? 1 : collisions;
	}
}