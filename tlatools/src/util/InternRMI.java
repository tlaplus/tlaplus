// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Mon Jan  1 23:19:07 PST 2001 by yuanyu

package util;

import java.io.*;
import java.rmi.*;

public interface InternRMI extends Remote {
  public UniqueString intern(String str) throws RemoteException;
}
