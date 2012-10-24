// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.distributed.fp;

import tlc2.tool.distributed.TLCWorker;

public class TLCWorkerAndFPSet {

	public static void main(final String[] args) {
		// Start distributed FPSet first
		new Thread(new Runnable() {
			/* (non-Javadoc)
			 * @see java.lang.Runnable#run()
			 */
			public void run() {
				DistributedFPSet.main(args);
			}
		}, DistributedFPSet.class.getName()).start();

		// Start worker afterwards as it requires FPSets to be available
		new Thread(new Runnable() {
			/* (non-Javadoc)
			 * @see java.lang.Runnable#run()
			 */
			public void run() {
				TLCWorker.main(args);
			}
		}, TLCWorker.class.getName()).start();
	}
}
