// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:36 PST by lamport
//      modified on Sun Sep  3 10:33:35 PDT 2000 by yuanyu

package tlc2.tool.liveness;


public class BTGraphNode extends BEGraphNode {
  /**
   * BTGraphNode is a node in the behaviour graph. We're going to only
   * store fingerprints of states, rather than actual states. So, as
   * we encounter each state, we will calculate all the <>[] and []<>s
   * listed in our order of solution.  For each arrow we must record
   * the target node and the checkActions along it.
   */

  /**
   * The unique index for the tableau graph node. Bit 31 is used as
   * the "done" bit; bit 30 is used as the "dummy" bit. So, the
   * maximum size of tableau is 2^30.
   */
  private int tindex;

  public BTGraphNode(long fp, int index) {
    super(fp);
    this.tindex = index;
  }

  public final int getIndex() { return (this.tindex & 0x3FFFFFFF); }

  public final void setIndex(int index) {
    this.tindex = (this.tindex & 0xC0000000) | index;
  }

  public final boolean isDone() { return this.tindex < 0; }

  public final void setDone() { this.tindex |= 0x80000000; }

  public static BTGraphNode makeDummy(long fp) {
    return new BTGraphNode(fp, 0x40000000);
  }

  public final boolean isDummy() {
    return (this.tindex & 0x40000000) > 0;
  }
  
  public final boolean equals(Object obj) {
    return ((obj instanceof BTGraphNode) &&
	    (this.stateFP == ((BTGraphNode)obj).stateFP) &&
	    (this.getIndex() == ((BTGraphNode)obj).getIndex()));
  }

  public final TBGraphNode getTNode(TBGraph tableau) {
    return tableau.getNode(this.getIndex());
  }
  
  public final String nodeInfo() {
    return "<" + this.stateFP + "," + this.getIndex() + ">";
  }

  /**
   * This method assumes that the visited field of all the nodes is
   * set to the same value. It flips the visited field. We use the
   * high-order bit of this.number as the visited bit.
   */
  protected final void toString(StringBuffer buf, boolean unseen) {
    if (this.getVisited() == unseen) {
      this.flipVisited();
      buf.append("(" + this.stateFP + "," + this.getIndex() + ") --> ");
      int size = this.nextSize();
      if (size != 0) {
	BTGraphNode node = (BTGraphNode)this.nextAt(0);
	buf.append("(" + node.stateFP + "," + node.getIndex() + ")");
      }
      for (int i = 1; i < size; i++) {
	buf.append(", ");
	BTGraphNode node = (BTGraphNode)this.nextAt(i);
	buf.append("(" + node.stateFP + "," + node.getIndex() + ")");
      }
      buf.append("\n");
      for (int i = 0; i < size; i++) {
	this.nextAt(i).toString(buf, unseen);
      }
    }
  }
  
}
