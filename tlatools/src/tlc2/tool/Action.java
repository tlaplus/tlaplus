// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.tool;

import java.io.Serializable;

import tla2sany.semantic.SemanticNode;
import tlc2.util.Context;
import util.UniqueString;

public final class Action implements ToolGlobals, Serializable {
  /* A TLA+ action.   */

  /* Fields  */
  public final SemanticNode pred;     // Expression of the action
  public final Context con;           // Context of the action
  private final UniqueString actionName;

  /* Constructors */
  public Action(SemanticNode pred, Context con) {
	  this(pred, con, (UniqueString) null);
  }

  public Action(SemanticNode pred, Context con, UniqueString actionName) {
	  this.pred = pred;
	  this.con = con;
	  this.actionName = actionName;
  }

/* Returns a string representation of this action.  */
  public final String toString() {
    return "<Action " + pred.toString() + ">";
  }

  public final String getLocation() {
	  if (actionName != null && !"".equals(actionName.toString())) {
		  // If known, print the action name instead of the generic string "Action".
	      return "<" + actionName + " " +  pred.getLocation() + ">";
	  }
	  return "<Action " + pred.getLocation() + ">";
  }
}
