// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:38 PST by lamport
//      modified on Sun Aug  5 00:14:58 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.Vect;

class LNDisj extends LiveExprNode {
  protected Vect disjs;   // The disjuncts
  protected int info;

  public LNDisj(int size) {
    this.disjs = new Vect(size);
    this.info = 0;
  }

  public LNDisj(LiveExprNode n) {
    this.disjs = new Vect(1);
    this.disjs.addElement(n);
    int level = n.getLevel();
    this.info = n.containAction() ? level+8 : level;
  }

  public LNDisj(LiveExprNode n1, LiveExprNode n2) {
    this.disjs = new Vect(2);
    this.disjs.addElement(n1);
    this.disjs.addElement(n2);
    boolean hasAct = n1.containAction() || n2.containAction();
    int level = Math.max(n1.getLevel(), n2.getLevel());
    this.info = hasAct ? level+8 : level;
  }

  public LNDisj(Vect disjs) {
    this.disjs = disjs;
    boolean hasAct = false;
    int level = 0;
    for (int i = 0; i < disjs.size(); i++) {
      LiveExprNode lexpr = (LiveExprNode)disjs.elementAt(i);
      level = Math.max(level, lexpr.getLevel());
      hasAct = hasAct || lexpr.containAction();
    }
    this.info = hasAct ? level+8 : level;
  }
  
  public final int getCount() { return this.disjs.size(); }

  public final LiveExprNode getBody(int i) {
    return (LiveExprNode)this.disjs.elementAt(i);
  }

  public final void addDisj(LiveExprNode elem) {
    if (elem instanceof LNDisj) {
      LNDisj elem1 = (LNDisj)elem;
      for (int i = 0; i < elem1.getCount(); i++) {
	this.addDisj(elem1.getBody(i));
      }
    }
    else {
      this.disjs.addElement(elem);
    }
    int level = Math.max(this.getLevel(), elem.getLevel());
    boolean hasAct = this.containAction() || elem.containAction();
    this.info = hasAct ? level+8 : level;
  }

  public final int getLevel() { return (this.info & 7); }

  public final boolean containAction() { return (this.info & 8) > 0; }

  public final boolean eval(Tool tool, TLCState s1, TLCState s2) {
    int sz = disjs.size();
    for (int i = 0; i < sz; i++) {
      LiveExprNode item = (LiveExprNode)disjs.elementAt(i);
      if (item.eval(tool, s1, s2)) return true;
    }
    return false;
  }
  
  public final void toString(StringBuffer sb, String padding) {
    int len = this.getCount();
    String padding1 = padding + "    ";
    for (int i = 0; i < len; i++) {
      if (i != 0) {
	sb.append(padding);
      }
      sb.append("\\/ (");
      this.getBody(i).toString(sb, padding1);
      sb.append(")");
      if (i != len-1) {
	sb.append("\n");
      }
    }
  }
}

