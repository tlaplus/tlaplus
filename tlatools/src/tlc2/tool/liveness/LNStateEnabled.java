// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:15 PST by lamport
//      modified on Sat Jul 28 00:36:53 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tla2sany.semantic.ExprNode;
import tlc2.tool.ActionItemList;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateFun;
import tlc2.tool.Tool;
import tlc2.util.Context;

class LNStateEnabled extends LNState {
  protected ExprNode pred;
  protected ExprNode subscript;
  protected boolean isBox;

  public LNStateEnabled(ExprNode pred, Context con, ExprNode subscript, boolean isBox) {
    super(con);
    this.pred = pred;
    this.subscript = subscript;
    this.isBox = isBox;
  }

  public final boolean eval(Tool tool, TLCState s1, TLCState s2) {
    // Note that s2 is useless.
    if (this.isBox && this.subscript != null) return true;

    ActionItemList acts = ActionItemList.Empty;
    TLCState sfun = TLCStateFun.Empty;
    Context c1 = Context.branch(this.con);
    if (this.subscript != null) {
      acts = acts.cons(this.subscript, c1, -3);
    }    
    sfun = tool.enabled(this.pred, acts, c1, s1, sfun);
    return sfun != null;
  }

  public final void toString(StringBuffer sb, String padding) {
    sb.append("ENABLED ");
    if (this.subscript == null) {
      this.pred.toString(sb, padding + "        ");
    }
    else {
      sb.append((this.isBox) ? "[" : "<");
      this.pred.toString(sb, padding + "         ");
      sb.append(((this.isBox) ? "]_" : ">_") + this.subscript);
    }
  }  
}

