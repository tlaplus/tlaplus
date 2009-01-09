// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:50 PST by lamport
//      modified on Sun Aug  5 00:16:15 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.SetOfLong;
import tlc2.util.Vect;

public class TBGraphNode {
  /**
   * TBGraphNode represents a node in the tableau graph. Read MP for
   * what a particle tableau graph is. We give each node in the
   * tableau-graph an index because it might be useful for hashing.
   * statePreds are deduced from the particle at the moment of
   * creation.  They are later used in checking if a state-node is
   * consistent with a tableau-node.
   */
  private TBPar par;            // particle
  public Vect nexts;            // outlinks
  public int index;             // unique id for this node
  private LiveExprNode[] statePreds;  // state predicates in the particle

  public static TBGraphNode dummyNode = new TBGraphNode();
  
  private TBGraphNode() {
    this.par = null;
    this.nexts = null;
    this.index = -1;
    this.statePreds = null;
  }
  
  public TBGraphNode(TBPar par) {
    this.par = par;
    this.index = 0;
    this.nexts = new Vect();
    TBPar preds = new TBPar(par.size());
    for (int i = 0; i < par.size(); i++) {
      LiveExprNode ln = par.exprAt(i);
      if (ln instanceof LNState) {
	preds.addElement(ln);
      }
      else if (ln instanceof LNNeg) {
	LiveExprNode body = ((LNNeg)ln).getBody();
	if (body instanceof LNState) {
	  preds.addElement(ln);
	}
      }
    }
    this.statePreds = new LiveExprNode[preds.size()]; 
    for (int i = 0; i < preds.size(); i++) {
      this.statePreds[i] = (LiveExprNode)preds.exprAt(i);
    }
  }

  public final TBPar getPar() { return this.par; }

  public final int nextSize() { return this.nexts.size(); }
  
  public final TBGraphNode nextAt(int i) {
    return (TBGraphNode)this.nexts.elementAt(i);
  }

  public final boolean hasLink(TBGraphNode target) {
    int sz = this.nexts.size();
    for (int i = 0; i < sz; i++) {
      if (this.nexts.elementAt(i) == target)
	return true;
    }
    return false;
  }
  
  /* Checks if this particle node is consistent with a state.  */
  public final boolean isConsistent(TLCState state, Tool tool) {
    for (int j = 0; j < this.statePreds.length; j++) {
      if (!this.statePreds[j].eval(tool, state, null)) {
	return false;
      }
    }
    return true;
  }

  public final String toString() {
    StringBuffer buf = new StringBuffer();
    SetOfLong visited = new SetOfLong(16);
    this.toString(buf, visited);
    return buf.toString();
  }

  private final void toString(StringBuffer buf, SetOfLong visited) {
    if (!visited.put(this.index)) {
      buf.append(this.par.toString());
      for (int i = 0; i < this.nexts.size(); i++) {
	buf.append(this.nextAt(i).index + " ");
      }
      buf.append("\n");
      for (int i = 0; i < this.nexts.size(); i++) {
	this.nextAt(i).toString(buf, visited);
      }
    }
  }

}

