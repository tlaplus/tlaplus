// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package org.lamport.tlatools.impl.distributed;

import java.net.URI;

import tlc2.ITLCWorker;
import tlc2.tool.distributed.TLCWorker;

public class TLCWorkerWrapper extends TLCWrapper implements ITLCWorker {

	/* (non-Javadoc)
	 * @see tlc2.ITLCWorker#connect(java.net.URI)
	 */
	public boolean connect(final URI uri) {
		super.connect("TLCWorker");
		try {
			TLCWorker.main(new String[] { uri.getHost() });
		} catch(Exception e) {
			// not expected to happen
			e.printStackTrace();
			return false;
		}
		return true;
	}

	/* (non-Javadoc)
	 * @see tlc2.ITLCWorker#disconnect()
	 */
	public boolean disconnect() {
		try {
			TLCWorker.shutdown();
		} catch (Exception e) {
			// not expected to happen
			e.printStackTrace();
			return false;
		}
		return true;
	}
}
