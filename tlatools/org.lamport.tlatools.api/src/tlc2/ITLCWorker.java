// Copyright (c) 2011 Microsoft Corporation.  All rights reserved.
package tlc2;

import java.net.URI;

public interface ITLCWorker {

	/**
	 * Connects this {@link ITLCWorker} to a TLCServer at the given target {@link URI} 
	 * @param uri The target {@link URI}
	 * @return true iff connected successfully
	 */
	boolean connect(URI uri);
	
	/**
	 * Block the caller for as long as the connected worker is computing. The
	 * behavior on calling this on a disconnected worker is undefined.
	 */
	void awaitTermination();
	
	/**
	 * Disconnects from the remote TLCServer
	 * @return true iff disconnected successfully
	 */
	boolean disconnect();
}
