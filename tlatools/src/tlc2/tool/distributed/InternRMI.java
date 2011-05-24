// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Mon Jan  1 23:19:07 PST 2001 by yuanyu

package tlc2.tool.distributed;

import java.rmi.Remote;
import java.rmi.RemoteException;

import util.UniqueString;

public interface InternRMI extends Remote {
	public UniqueString intern(String str) throws RemoteException;
}
