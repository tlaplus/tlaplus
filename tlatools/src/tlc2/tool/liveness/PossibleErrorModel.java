// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:49 PST by lamport
//      modified on Sat Mar 25 22:39:46 PST 2000 by yuanyu

package tlc2.tool.liveness;


public class PossibleErrorModel {
  int[] EAAction;    // <>[]act's
  int[] AEState;     // []<>state's
  int[] AEAction;    // []<>act's

  public final boolean isEmpty() {
    return (this.EAAction.length == 0 &&
	    this.AEState.length == 0 &&
	    this.AEAction.length == 0);
  }
  
  public final String toString(LiveExprNode[] checkState,
			       LiveExprNode[] checkAction) {
    StringBuffer sb = new StringBuffer();
    this.toString(sb, "", checkState, checkAction);
    return sb.toString();
  }

  public final void toString(StringBuffer sb,
			     String padding,
			     LiveExprNode[] checkState,
			     LiveExprNode[] checkAction) {
    boolean noPadding = true;
    String padding1 = padding + "       ";

    for (int i = 0; i < this.EAAction.length; i++) {
      int idx = this.EAAction[i];
      if (noPadding) {
	noPadding = false;
      }
      else {
	sb.append(padding);
      }
      sb.append("/\\ <>[]");
      checkAction[idx].toString(sb, padding1);
      sb.append("\n");
    }
    for (int i = 0; i < this.AEState.length; i++) {
      int idx = this.AEState[i];
      if (noPadding) {
	noPadding = false;
      }
      else {
	sb.append(padding);
      }      
      sb.append("/\\ []<>");
      checkState[idx].toString(sb, padding1);
      sb.append("\n");
    }
    for (int i = 0; i < this.AEAction.length; i++) {
      int idx = this.AEAction[i];
            if (noPadding) {
	noPadding = false;
      }
      else {
	sb.append(padding);
      }
      sb.append("/\\ []<>");
      checkAction[idx].toString(sb, padding1);
      sb.append("\n");
    }
  }

}

