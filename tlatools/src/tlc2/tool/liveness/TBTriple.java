// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:53 PST by lamport
//      modified on Thu Sep 21 22:17:17 PDT 2000 by yuanyu

package tlc2.tool.liveness;

public class TBTriple {
  /**
   * TBTriple are used in tableau construction.  There are two kinds
   * of triples. The alpha triples are (p/\q, p, q) and ([]p, p, O[]p).
   * The beta triples are (p\/q, p, q) and (<>p, p, O<>q).
   */
  private LiveExprNode fa;
  private LiveExprNode fb;
  private LiveExprNode fc;

  public TBTriple(LiveExprNode a, LiveExprNode b, LiveExprNode c) {
    this.fa = a;
    this.fb = b;
    this.fc = c;
  }
  public final LiveExprNode getA() { return this.fa; }
  public final LiveExprNode getB() { return this.fb; }
  public final LiveExprNode getC() { return this.fc; }

  public final boolean isAlpha() {
    return ((this.fa instanceof LNConj) ||
	    (this.fa instanceof LNAll));
  }

  public final boolean isBeta() {
    return ((this.fa instanceof LNDisj) ||
	    (this.fa instanceof LNEven));
  }

  public final String toString() {
    return "<" + this.fa + ",\n " + this.fb + ",\n " + this.fc + ">";
  }

}
