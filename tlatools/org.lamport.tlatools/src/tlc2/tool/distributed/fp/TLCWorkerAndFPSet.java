// Copyright (c) 2012 Markus Alexander Kuppe. All rights reserved.
package tlc2.tool.distributed.fp;

import tlc2.tool.distributed.TLCWorker;

public class TLCWorkerAndFPSet {

    public static void main(final String[] args) {
        // Start distributed FPSet first
        /* (non-Javadoc)
         * @see java.lang.Runnable#run()
         */
        new Thread(() -> DistributedFPSet.main(args), DistributedFPSet.class.getName()).start();

        // Start worker afterwards as it requires FPSets to be available
        /* (non-Javadoc)
         * @see java.lang.Runnable#run()
         */
        new Thread(() -> TLCWorker.main(args), TLCWorker.class.getName()).start();
    }
}
