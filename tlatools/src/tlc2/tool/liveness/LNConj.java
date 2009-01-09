// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:14 PST by lamport
//      modified on Sun Aug  5 00:13:41 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.Vect;

class LNConj extends LiveExprNode {
  protected Vect conjs;   // The conjuncts
  protected int info;
  
  public LNConj(int size) {
    this.conjs = new Vect(size);
    this.info = 0;
  }

  public LNConj(LiveExprNode n) {
    this.conjs = new Vect(1);
    this.conjs.addElement(n);
    int level = n.getLevel();
    this.info = n.containAction() ? level+8 : level;
  }

  public LNConj(LiveExprNode n1, LiveExprNode n2) {
    this.conjs = new Vect(2);
    this.conjs.addElement(n1);
    this.conjs.addElement(n2);
    boolean hasAct = n1.containAction() || n2.containAction();
    int level = Math.max(n1.getLevel(), n2.getLevel());
    this.info = hasAct ? level+8 : level;
  }

  public LNConj(Vect conjs) {
    this.conjs = conjs;
    boolean hasAct = false;
    int level = 0;
    for (int i = 0; i < conjs.size(); i++) {
      LiveExprNode lexpr = (LiveExprNode)conjs.elementAt(i);
      level = Math.max(level, lexpr.getLevel());
      hasAct = hasAct || lexpr.containAction();
    }
    this.info = hasAct ? level+8 : level;
  }
  
  public final int getCount() { return this.conjs.size(); }
  
  public final LiveExprNode getBody(int i) {
    return (LiveExprNode)this.conjs.elementAt(i);
  }

  public final void addConj(LiveExprNode elem) {
    if (elem instanceof LNConj) {
      LNConj elem1 = (LNConj)elem;
      for (int i = 0; i < elem1.getCount(); i++) {
	this.addConj(elem1.getBody(i));
      }
    }
    else {
      this.conjs.addElement(elem);
    }
    int level = Math.max(this.getLevel(), elem.getLevel());
    boolean hasAct = this.containAction() || elem.containAction();
    this.info = hasAct ? level+8 : level;
  }

  public final int getLevel() { return (this.info & 7); }

  public final boolean containAction() { return (this.info & 8) > 0; }

  public final boolean eval(Tool tool, TLCState s1, TLCState s2) {
    int sz = this.conjs.size();
    for (int i = 0; i < sz; i++) {
      LiveExprNode item = (LiveExprNode)this.conjs.elementAt(i);
      if (!item.eval(tool, s1, s2)) return false;
    }
    return true;
  }

  public final void toString(StringBuffer sb, String padding) {
    int len = this.getCount();
    String padding1 = padding + "    ";
    for (int i = 0; i < len; i++) {
      if (i != 0) {
	sb.append(padding);
      }
      sb.append("/\\ (");
      this.getBody(i).toString(sb, padding1);
      sb.append(")");
      if (i != len-1) {
	sb.append("\n");
      }
    }
  }
}
