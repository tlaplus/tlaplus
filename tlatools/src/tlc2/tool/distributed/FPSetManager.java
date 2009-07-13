// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:13:43 PST by lamport
//      modified on Wed Jan 10 00:09:44 PST 2001 by yuanyu

package tlc2.tool.distributed;

import java.io.IOException;
import java.io.Serializable;
import java.net.InetAddress;
import java.net.MalformedURLException;
import java.rmi.Naming;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;

import tlc2.util.BitVector;
import tlc2.util.LongVec;
import util.ToolIO;

/**
 * @deprecated not used currently
 * @author Simon Zambrovski
 * @version $Id$
 */
public class FPSetManager implements Serializable {

  private String[] hosts;     // The names of fpset servers
  private FPSetRMI[] fpSets;  // the list of fpset servers

  // SZ Jul 13, 2009: moved from FPSetRMI
  public static int Port = 10998; // port # for fpset server

  
  public FPSetManager(FPSetRMI fpSet) {
    this.hosts = new String[1];
    this.hosts[0] = "localhost";
    this.fpSets = new FPSetRMI[1];
    this.fpSets[0] = fpSet;
  }
  
  /**
   * Constructed from a list of hostnames of fpset servers.  We require
   * that all the fp servers be available initially.
   */
  public FPSetManager(String[] hosts)
  throws RemoteException, NotBoundException, MalformedURLException {
    this.hosts = hosts;
    this.fpSets = new FPSetRMI[hosts.length];
    for (int i = 0; i < hosts.length; i++) {
      String url = "//" + hosts[i] + ":" + Port + "/FPSetServer";
      this.fpSets[i] = (FPSetRMI)Naming.lookup(url);
    }
  }

  public final int numOfServers() { return this.fpSets.length; }

  private final int reassign(int i) {
    int next = (i+1) % this.fpSets.length;
    while (next != i) {
      FPSetRMI fpSet = this.fpSets[next];
      if (fpSet != null) {
	String host = this.hosts[next];
	for (int j = i; j < next; j++) {
	  this.fpSets[j] = fpSet;
	  this.hosts[j] = host;
	}
	return next;
      }
      next = (next+1) % this.fpSets.length;
    }
    return -1;
  }

  public final void close(boolean cleanup) throws IOException {
    FPSetRMI curr = null;
    int len = this.fpSets.length;
    int idx = 0, lidx = 0;

    for (idx = 0; idx < len; idx++) {
      curr = this.fpSets[idx];
      if (curr != null) break;
    }
    if (curr == null) return;
    
    for (lidx = len-1; lidx > idx; lidx--) {
      FPSetRMI last = this.fpSets[lidx];
      if (last != null && last != curr) break;
    }
    for (int i = idx+1; i <= lidx; i++) {
      FPSetRMI next = this.fpSets[i];
      if (next != null && next != curr) {
	try { curr.exit(cleanup); } catch (Exception e) { /*SKIP*/ }
	curr = next;
      }
    }
    if (curr != null) {
      try { curr.exit(cleanup); } catch (Exception e) { /*SKIP*/ }      
    }
  }

  private final String getHostName() {
    String hostname = "Unknown";	
    try {
      hostname = InetAddress.getLocalHost().getHostName();
    }
    catch (Exception e) { /*SKIP*/ }
    return hostname;
  }
    
  public final boolean put(long fp) {
    int fpIdx = (int)((fp & 0x7FFFFFFFFFFFFFFFL) % this.fpSets.length);
    while (true) {
      try {
	return this.fpSets[fpIdx].put(fp);
      }
      catch (Exception e) {
	System.out.println("Warning: Failed to connect from " + this.getHostName() +
			   " to the fp server at " + this.hosts[fpIdx] +
			   ".\n" + e.getMessage());
	if (this.reassign(fpIdx) == -1) {
	    System.out.println("Warning: there is no fp server available.");	  
	  return false;
	}
      }
    }
  }
    
  public final BitVector[] putBlock(LongVec[] fps) {
    int len = this.fpSets.length;
    BitVector[] res = new BitVector[len];
    for (int i = 0; i < len; i++) {
      try {
	res[i] = this.fpSets[i].putBlock(fps[i]);
      }
      catch (Exception e) {
          System.out.println("Warning: Failed to connect from " + this.getHostName() +
			   " to the fp server at " + this.hosts[i] + ".\n" +
			   e.getMessage());
	if (this.reassign(i) == -1) {
	    System.out.println("Warning: there is no fp server available.");
	}
	res[i] = new BitVector(fps[i].size());
	res[i].set(0, fps[i].size()-1);
      }
    }
    return res;
  }
  
  public final BitVector[] containsBlock(LongVec[] fps) {
    int len = this.fpSets.length;
    BitVector[] res = new BitVector[len];
    for (int i = 0; i < len; i++) {
      try {
	res[i] = this.fpSets[i].containsBlock(fps[i]);
      }
      catch (Exception e) {
          System.out.println("Warning: Failed to connect from " + this.getHostName() +
			   " to the fp server at " + this.hosts[i] + ".\n" +
			   e.getMessage());
	if (this.reassign(i) == -1) {
	    System.out.println("Warning: there is no fp server available.");
	}
	res[i] = new BitVector(fps[i].size());
	res[i].set(0, fps[i].size()-1);
      }
    }
    return res;
  }

  public final long size() {
    int len = this.fpSets.length;    
    int res = 0;
    for (int i = 0; i < len; i++) {
      try {
	res += this.fpSets[i].size();
      }
      catch (Exception e) {
          System.out.println("Warning: Failed to connect from " + this.getHostName() +
			   " to the fp server at " + this.hosts[i] + ".\n" +
			   e.getMessage());
	if (this.reassign(i) == -1) {
	    System.out.println("Warning: there is no fp server available.");
	}
      }
    }
    return res;
  }
  
  private final void chkptInner(String fname, boolean chkpt)
  throws InterruptedException {
    int len = this.fpSets.length;
    Checkpoint[] chkpts = new Checkpoint[len];
    FPSetRMI curr = null;
    int cnt = 0, idx = 0, lidx = 0;

    for (idx = 0; idx < len; idx++) {
      curr = this.fpSets[idx];
      if (curr != null) {
	chkpts[cnt] = new Checkpoint(idx, fname, chkpt);
	chkpts[cnt].run();
	cnt++;
	break;
      }
    }
    if (curr == null) return;

    for (lidx = len-1; lidx > idx; lidx--) {
      FPSetRMI last = this.fpSets[lidx];
      if (last != null && last != curr) break;
    }

    for (int i = idx+1; i <= lidx; i++) {
      FPSetRMI next = this.fpSets[i];
      if (next != null && next != curr) {
	curr = next;
	chkpts[cnt] = new Checkpoint(i, fname, chkpt);
	chkpts[cnt].run();
	cnt++;
      }
    }

    for (int i = 0; i < cnt; i++) {
      chkpts[i].join();
    }
  }
  
  public final void checkpoint(String fname) throws InterruptedException {
    chkptInner(fname, true);
  }
  
  public final void recover(String fname) throws InterruptedException {
    chkptInner(fname, false);
  }

  final class Checkpoint extends Thread {
    int hostIndex;
    String filename;
    boolean isChkpt;

    public Checkpoint(int index, String fname, boolean chkpt) {
      this.hostIndex = index;
      this.filename = fname;
      this.isChkpt = chkpt;
    }
    
    public void run() {
      try {
	if (this.isChkpt) {
	  fpSets[this.hostIndex].beginChkpt(this.filename);
	  fpSets[this.hostIndex].commitChkpt(this.filename);
	}
	else {
	  fpSets[this.hostIndex].recover(this.filename);
	}
      }
      catch (IOException e) {
	ToolIO.err.println("Error: Failed to checkpoint the fingerprint server at " +
			   hosts[this.hostIndex] + ". This server might be down.");
      }
    }
  }
  
}
