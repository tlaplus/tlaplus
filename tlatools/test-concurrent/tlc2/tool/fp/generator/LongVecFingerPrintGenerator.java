// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp.generator;

import java.io.IOException;
import java.util.Arrays;
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
		TestLongVec predecessors = new TestLongVec(batch);
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
	
	// This implementation adds two methods that should be used with caution as
	// they mess with the internal capacity checks of LongVec. We don't want to
	// make them API.
	private class TestLongVec extends LongVec {

		private static final long serialVersionUID = -720614225756936980L;

		public TestLongVec(int batch) {
			super(batch);
		}

		public final void sort() {
			Arrays.sort(elementData);
		}
		  
		public final void setElement(int index, long x) {
			this.elementData[index] = x;
			this.elementCount = ++elementCount % elementData.length + 1;
		}
	}
}