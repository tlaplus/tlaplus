// Copyright (c) 2012 Microsoft Corporation.  All rights reserved.

package tlc2.tool.distributed.fp;

import java.rmi.RemoteException;

@SuppressWarnings("serial")
public class FPSetManagerException extends RemoteException {

	public FPSetManagerException(String s) {
		super(s);
	}
}
