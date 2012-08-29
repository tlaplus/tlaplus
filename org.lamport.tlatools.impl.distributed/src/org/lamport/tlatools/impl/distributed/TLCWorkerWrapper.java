// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package org.lamport.tlatools.impl.distributed;

import java.net.URI;
import java.rmi.NoSuchObjectException;

import tlc2.ITLCWorker;
import tlc2.tool.distributed.RMIFilenameToStreamResolver;
import tlc2.tool.distributed.TLCWorker;

public class TLCWorkerWrapper implements ITLCWorker {

	private TLCWorker[] tlcWorker;

	/* (non-Javadoc)
	 * @see tlc2.ITLCWorker#connect(java.net.URI)
	 */
	public boolean connect(URI uri) {
		try {
			final RMIFilenameToStreamResolver aFTS = new OSGiNameToFileIStream();
			TLCWorker.setFilenameToStreamResolver(aFTS);
			TLCWorker.main(new String[] { uri.getHost() });
			tlcWorker = TLCWorker.getTLCWorker();
		} catch(Exception e) {
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
			for (TLCWorker w : tlcWorker) {
				w.exit();
			}
		} catch (NoSuchObjectException e) {
			e.printStackTrace();
			return false;
		} catch (NullPointerException e) {
			e.printStackTrace();
			return false;
		}
		return true;
	}
}
