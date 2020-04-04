// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2;

import java.net.URI;

public interface IDistributedFPSet {

	/**
	 * Connects this {@link IDistributedFPSet} to a TLCServer/FPSetManager at the given target {@link URI} 
	 * @param uri The target {@link URI}
	 * @return true iff connected successfully
	 */
	boolean connect(URI uri);

	/**
	 * Disconnects from the remote TLCServer/FPSetManager
	 * @return true iff disconnected successfully
	 */
	boolean disconnect();
}
