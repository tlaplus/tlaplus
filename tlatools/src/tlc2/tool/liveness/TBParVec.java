// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:53 PST by lamport
//      modified on Thu Sep 21 15:39:03 PDT 2000 by yuanyu

package tlc2.tool.liveness;

import tlc2.util.Vect;

public class TBParVec extends Vect {

  public TBParVec(int size) { super(size); }

  public final TBPar parAt(int i) { return (TBPar)elementAt(i); }

  /* This method tests whether a particle is in a list of other particles */
  public final boolean contains(TBPar par) {
    for (int i = 0; i < this.size(); i++) {
      if (par.equals(this.parAt(i))) return true;
    }
    return false;
  }

  /* This method unions two lists of particles */
  public final TBParVec union(TBParVec ps) {
    TBParVec res = new TBParVec(this.size()+ps.size());
    for (int i = 0; i < this.size(); i++) {
      if (!ps.contains(this.parAt(i)))
	res.addElement(this.parAt(i));
    }
    for (int i = 0; i < ps.size(); i++) {
      res.addElement(ps.parAt(i));
    }
    return res;
  }

  /* The string representation. */
  public final void toString(StringBuffer sb, String padding) {
    sb.append("{");
    String padding1 = padding + " ";
    if (this.size() != 0) {
      this.parAt(0).toString(sb, padding1);
    }
    for (int i = 1; i < this.size(); i++) {
      sb.append(",\n");
      sb.append(padding1);
      this.parAt(i).toString(sb, padding1);
    }
    sb.append("}");
  }

  public final String toString() {
    StringBuffer sb = new StringBuffer();
    this.toString(sb, "");
    return sb.toString();
  }

}
