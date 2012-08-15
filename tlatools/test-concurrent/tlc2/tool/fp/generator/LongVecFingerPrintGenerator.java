// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package tlc2.tool.fp.generator;

import java.io.IOException;
import java.util.concurrent.CountDownLatch;

import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.MultiThreadedFPSetTest;
import tlc2.util.BitVector;
import tlc2.util.LongVec;

public class LongVecFingerPrintGenerator extends FingerPrintGenerator {

	private static final int batch = 1024;
	
	public LongVecFingerPrintGenerator(MultiThreadedFPSetTest test, int id, FPSet fpSet, CountDownLatch latch, long seed, long insertions) {
		super(test, id, fpSet, latch, seed, insertions);
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		LongVec predecessors = new LongVec(batch);
		boolean initialized = false;
		while (fpSet.size() < insertions) {
			try {
				// Make sure set still contains predecessors
				if (initialized) {
					final BitVector bitVector = fpSet.containsBlock(predecessors);
					MultiThreadedFPSetTest.assertTrue(bitVector.trueCnt() == batch);
				}

				// Fill new fingerprints and sort them
				for (int i = 0; i < batch; i++) {
					predecessors.setElement(i, rnd.nextLong());
				}
				initialized = true;
				predecessors.sort();

				// Add sorted batch to fpset
				final BitVector bitVector = fpSet.putBlock(predecessors);
				puts += bitVector.trueCnt();
				collisions += (batch - bitVector.trueCnt());

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
}