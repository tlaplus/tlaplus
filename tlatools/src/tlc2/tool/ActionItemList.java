// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.tool;

import tla2sany.semantic.SemanticNode;
import tlc2.util.Context;

public class ActionItemList {
  /**
   * We assume that this.pred is null iff the list is empty.
   * The meaning of this.kind is given as follows:
   *    kind > 0:  pred of a conjunction
   *    kind = -1: pred
   *    kind = -2: UNCHANGED pred
   *    kind = -3: pred' # pred
   */
  public SemanticNode pred;     // Expression of the action
  public Context con;           // Context of the action
  public int kind;  
  public ActionItemList next;

  public final static ActionItemList
    Empty = new ActionItemList(null, null, 0, null);
  
  /* Constructors */
  private ActionItemList(SemanticNode pred, Context con,
			 int kind, ActionItemList next) {
    this.pred = pred;
    this.con = con;
    this.kind = kind;
    this.next = next;
  }

  public final SemanticNode carPred() { return this.pred; }

  public final Context carContext() { return this.con; }

  public final int carKind() { return this.kind; }

  public final ActionItemList cdr() { return this.next; }

  public final ActionItemList cons(SemanticNode pred,
				   Context con, int kind) {
    return new ActionItemList(pred, con, kind, this);
  }

  public final boolean isEmpty() { return this == Empty; }
  
}
