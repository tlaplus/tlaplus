// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tlc2.tool;

import tla2sany.semantic.SemanticNode;
import tla2sany.st.Location;

public class CallStack {
  /* A trace of function calls.  */

  public CallStack() {
    this.stack = new SemanticNode[64];
    this.index = 0;
  }

  private SemanticNode[] stack;    // the call stack
  private int index;               // pointer to the empty slot
  private boolean frozen;

  public final void push(SemanticNode expr) {
    if (this.index == this.stack.length) {
      this.resize();
    }
    this.stack[this.index++] = expr;
  }

  public final void pop() { if(!frozen) this.index--; }

  /**
   * Calling freeze turns all subsequent pop operations into no-ops. 
   */
  public void freeze() {
	  this.frozen = true;
  }
  
  public final int size() { return this.index; }

  private final void resize() {
    int len = 2 * this.stack.length;
    SemanticNode[] stack1 = new SemanticNode[len];
    System.arraycopy(this.stack, 0, stack1, 0, this.stack.length);
    this.stack = stack1;
  }

  // Returns a string representation of this.
  public final String toString()
  {
    /*
     * Moved in the distinction if the call stack is empty or not (from Tool)
     */
    if (this.index > 0)
    {
      final StringBuffer sb = new StringBuffer();
      SemanticNode expr = null;
      int stackDepth = 0;
      for (int i = 0; i < this.index; i++) {
        if(expr == this.stack[i]) {
        	// Skip consecutive identical SemanticNodes.
        	continue;
        }
        expr = this.stack[i];
        Location loc = expr.getTreeNode().getLocation();
        sb.append(stackDepth + ". ");
        sb.append("Line ");
        sb.append(loc.beginLine());
        sb.append(", column ");
        sb.append(loc.beginColumn());
        sb.append(" to line ");
        sb.append(loc.endLine());
        sb.append(", column ");
        sb.append(loc.endColumn());
        sb.append(" in ");
        sb.append(loc.source() + "\n");
        stackDepth++;
      }
      sb.append("\n");
      return sb.toString();
    } else {
        return "    The error call stack is empty.\n";
    }
  }

}
