// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.fp;

import java.util.Random;

import tlc2.tool.distributed.TLCWorker;

/**
 * This main class starts worker (compute) and fingerprints (storage) nodes and
 * crashes them randomly to simulate node failures.
 */
public class FailingTLCWorkerAndFPSet {

	@SuppressWarnings("deprecation")
	public static void main(final String[] args) throws InterruptedException {
		final Random rnd = new Random();

		Thread workers = null;
		Thread dfs = null;
		
		// Never end which is only acceptable in a test deployment where an
		// external instance kills this main thread. 
		while (true) {

			// Start distributed FPSet first if null
			if (dfs == null) {
				dfs = new Thread(new Runnable() {
					/* (non-Javadoc)
					 * @see java.lang.Runnable#run()
					 */
					public void run() {
						DistributedFPSet.main(args);
					}
				}, DistributedFPSet.class.getName());
				dfs.start();
			}
			
			// Start worker afterwards as it requires FPSets to be available
			if (workers == null) {
				workers = new Thread(new Runnable() {
					/* (non-Javadoc)
					 * @see java.lang.Runnable#run()
					 */
					public void run() {
						TLCWorker.main(args);
					}
				}, TLCWorker.class.getName());
				workers.start();
			}
			
			// Calculate a random sleep time between 1 and 10 minutes
			int sleep = (rnd.nextInt(9) + 1) ;
			System.err.println("Sleeping for " + sleep + " minutes...");
			Thread.sleep(sleep * 1000 * 60);
			
			// Decide to either kill workers, dfs or both
			int action = rnd.nextInt(2);
			switch (action) {
				case 0:
					System.err.println("Doing nothing...");
					break;
				case 1:
					System.err.println("Killing fingerprint server...");
					dfs.stop();
					dfs = null;
					// Try to reclaim the heap used by dfs
					System.gc();
					break;
				// TODO support case 2,3,4 (2 & 3 fail due to TLC limitations of
				// only one run per JVM. Use OSGi based worker as a workaround)
				case 2:
					System.err.println("Killing workers...");
					workers.stop();
					workers = null;
					break;
				case 3:
					System.err.println("Killing workers and fingerprint server...");
					workers.stop();
					workers = null;
					dfs.stop();
					dfs = null;
					// Try to reclaim the heap used by dfs
					System.gc();
					break;
				case 4:
					System.exit(1);
					break;
			}
			
			// Give master a one minute grace period to clean up
			Thread.sleep(1000 * 60);
		}
	}
}
