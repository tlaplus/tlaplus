// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tlatools.impl.distributed;

import java.net.URI;

import tlc2.IDistributedFPSet;
import tlc2.tool.distributed.fp.DistributedFPSet;

public class TLCDistributedFPSetWrapper extends TLCWrapper implements IDistributedFPSet {

	/* (non-Javadoc)
	 * @see tlc2.IDistributedFPSet#connect(java.net.URI)
	 */
	public boolean connect(URI uri) {
		super.connect("FPSet");
		try {
			DistributedFPSet.main(new String[] { uri.getHost() });
		} catch (Exception e) {
			// not expected to happen
			e.printStackTrace();
			return false;
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see tlc2.IDistributedFPSet#disconnect()
	 */
	public boolean disconnect() {
		try {
			DistributedFPSet.shutdown();
		} catch (Exception e) {
			// not expected to happen
			e.printStackTrace();
			return false;
		}
		return true;
	}
}
