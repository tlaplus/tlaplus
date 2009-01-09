// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:37 PST by lamport
//      modified on Mon Nov 26 15:46:11 PST 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.util.BitVector;

public class GraphNode {
  /**
   * GraphNode is a node in the behaviour graph. We're going to only
   * store fingerprints of states, rather than actual states. So, as
   * we encounter each state, we need to calculate all the <>[] and 
   * []<>'s listed in the order of solution.  For each outgoing edge,
   * we record the fingerprint of the target node and the checkActions
   * along it.
   *
   * The field tidx is the unique index for the tableau graph node. If
   * tindex = -1, then there is no tableau. So, the maximum size of
   * tableau is 2^31.
   */
  private final static int[] emptyIntArr = new int[0];
  
  public long stateFP;        // fingerprint of the state
  public int[] nnodes;        // outgoing links
  public BitVector checks;    // truth values for state and action preds
  public int tindex;

  public GraphNode(long fp, int tindex) {
    this.stateFP = fp;
    this.nnodes = emptyIntArr;
    this.checks = new BitVector(0);
    this.tindex = tindex;
  }

  public GraphNode(long fp, int tindex, int[] nnodes, BitVector checks) {
    this.stateFP = fp;
    this.nnodes = nnodes;
    this.checks = checks;
    this.tindex = tindex;
  }

  public final boolean equals(Object obj) {
    return ((obj instanceof GraphNode) &&
	    (this.stateFP == ((GraphNode)obj).stateFP) &&
	    (this.tindex == ((GraphNode)obj).tindex));
  }

  public final long getStateFP(int i) {
    long high = this.nnodes[3*i];
    long low = this.nnodes[3*i+1];
    return (high << 32) | (low & 0xFFFFFFFFL);
  }

  public final int getTidx(int i) { return this.nnodes[3*i+2]; }

  public final int succSize() { return this.nnodes.length/3; }
  
  public final boolean getCheckState(int i) {
    return this.checks.get(i);
  }
    
  public final boolean getCheckAction(int slen, int alen, int nodeIdx, int i) {
    int pos = slen + alen * nodeIdx + i;
    return this.checks.get(pos);
  }

  public final boolean getCheckAction(int slen, int alen, int nodeIdx, int[] is) {
    int len = is.length;
    for (int i = 0; i < len; i++) {
      int pos = slen + alen * nodeIdx + is[i];
      if (!this.checks.get(pos)) return false;
    }
    return true;
  }

  public final void setCheckState(boolean[] vals) {
    int len = vals.length;
    for (int i = 0; i < len; i++) {
      if (vals[i]) { this.checks.set(i); }
    }
  }

  /* Add a new transition to the node target. */
  public final void addTransition(long fp, int tidx, int slen,
				  int alen, boolean[] acts) {
    if (acts != null) {
      int pos = slen + alen * this.succSize();
      for (int i = 0; i < acts.length; i++) {
	if (acts[i]) { this.checks.set(pos+i); }
      }
    }
    int len = this.nnodes.length;
    int[] newNodes = new int[len+3];
    System.arraycopy(this.nnodes, 0, newNodes, 0, len);
    newNodes[len] = (int)(fp >>> 32);
    newNodes[len+1] = (int)(fp & 0xFFFFFFFFL);
    newNodes[len+2] = tidx;
    this.nnodes = newNodes;
  }

  /* Return true iff there is an outgoing edge to target. */
  public final boolean transExists(long fp, int tidx) {
    int len = this.nnodes.length;
    int high = (int)(fp >>> 32);
    int low = (int)(fp & 0xFFFFFFFFL);
    for (int i = 0; i < len; i += 3) {
      if (this.nnodes[i] == high &&
	  this.nnodes[i+1] == low &&
	  this.nnodes[i+2] == tidx) {
	return true;
      }
    }
    return false;
  }

  /* Return the tableau graph node used by this. */
  public final TBGraphNode getTNode(TBGraph tableau) {
    return tableau.getNode(this.tindex);
  }
    
  public final String toString() {
    StringBuffer buf = new StringBuffer();
    buf.append("<" + this.stateFP +  "," + this.tindex + "> --> ");
    int size = this.nnodes.length;
    if (size != 0) {
      long high = this.nnodes[0];
      long low = this.nnodes[1];
      long fp = (high << 32) | (low & 0xFFFFFFFFL);
      buf.append("<" + fp + "," + this.nnodes[0] + ">");
    }
    for (int i = 1; i < size; i += 3) {
      buf.append(", ");
      long high = this.nnodes[i];
      long low = this.nnodes[i+1];
      long fp = (high << 32) | (low & 0xFFFFFFFFL);
      buf.append("<" + fp + "," + this.nnodes[i] + ">");      
    }
    return buf.toString();
  }

}
