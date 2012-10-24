// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.fp.generator;

import java.io.IOException;
import java.util.Arrays;
import java.util.concurrent.CountDownLatch;

import tlc2.tool.fp.FPSet;
import tlc2.tool.fp.MultiThreadedFPSetTest;

public class BatchedFingerPrintGenerator extends FingerPrintGenerator {

	private static final int batch = 1024;
	
	public BatchedFingerPrintGenerator(MultiThreadedFPSetTest test, int id, FPSet fpSet, CountDownLatch latch, long seed, long insertions) {
		super(test, id, fpSet, latch, seed, insertions);
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Runnable#run()
	 */
	public void run() {
		long predecessors[] = new long[batch];
		boolean initialized = false;
		while (fpSet.size() < insertions) {
			try {
				// Make sure set still contains predecessors
				if (initialized) {
					for (int i = 0; i < predecessors.length; i++) {
						long predecessor = predecessors[i];
						MultiThreadedFPSetTest.assertTrue(fpSet.contains(predecessor));
					}
				}

				// Fill new fingerprints and sort them
				for (int i = 0; i < predecessors.length; i++) {
					predecessors[i] = rnd.nextLong();
				}
				initialized = true;
				Arrays.sort(predecessors);

				// Add sorted batch to fpset
				for (int i = 0; i < predecessors.length; i++) {
					long predecessor = predecessors[i];
					boolean put = fpSet.put(predecessor);
					if (put == false) {
						puts++;
					} else {
						collisions++;
					}
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
}