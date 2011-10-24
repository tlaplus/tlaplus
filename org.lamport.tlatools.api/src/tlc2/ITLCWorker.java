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
	 * Disconnects from the remote TLCServer
	 * @return true iff disconnected successfully
	 */
	boolean disconnect();
}
