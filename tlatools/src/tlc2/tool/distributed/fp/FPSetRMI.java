// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:13:35 PST by lamport
//      modified on Fri Dec 15 15:24:57 PST 2000 by yuanyu

package tlc2.tool.distributed.fp;

import java.io.IOException;
import java.rmi.Remote;
import java.rmi.RemoteException;

import tlc2.util.BitVector;
import tlc2.util.LongVec;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface FPSetRMI extends Remote {

	boolean put(long fp) throws IOException;

	boolean contains(long fp) throws IOException;

	BitVector putBlock(LongVec fpv) throws IOException;

	BitVector containsBlock(LongVec fpv) throws IOException;

	long size() throws IOException;

	void exit(boolean cleanup) throws IOException;

	void beginChkpt(String filename) throws IOException;

	void commitChkpt(String filename) throws IOException;

	void recover(String filename) throws IOException;

	/**
	 * @return The amount of states seen by this FPSet (not distinct states!)
	 */
	long getStatesSeen() throws RemoteException;

	double checkFPs() throws IOException;
}
