// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:50 PST by lamport
//      modified on Thu Sep 21 22:20:35 PDT 2000 by yuanyu

package tlc2.tool.liveness;

import tlc2.output.EC;
import tlc2.util.Vect;
import util.Assert;

public class TBPar extends Vect {

  public TBPar(int i) { super(i); }
  
  public final LiveExprNode exprAt(int i) {
    return (LiveExprNode)elementAt(i);
  }

  /* This method returns true iff this particle is equal to another particle */
  public final boolean equals(TBPar par) {
    return (this.contains(par) && par.contains(this));
  }

  /**
   * This method tests whether or not an expression is in a list of
   * expressions.
   */
  public final boolean member(LiveExprNode e) {
    for (int i = 0; i < this.size(); i++) {
      if (e.equals(this.exprAt(i))) return true;
    }
    return false;
  }

  /**
   * This method tests whether a particle par is a subset of this
   * particle.
   */
  public final boolean contains(TBPar par) {
    for (int i = 0; i < par.size(); i++) {
      if (!this.member(par.exprAt(i))) return false;
    }
    return true;
  }

  /* This method returns the unions of two particles.  */
  public final TBPar union(TBPar par) {
    TBPar res = new TBPar(this.size()+par.size());
    for (int i = 0; i < this.size(); i++) {
      if (!par.member(this.exprAt(i)))
	res.addElement(this.exprAt(i));
    }
    for (int i = 0; i < par.size(); i++) {
      res.addElement(par.exprAt(i));
    }
    return res;
  }

  /* This method appends an expression to the tail of Par.  */
  public final TBPar append(LiveExprNode ln) {
    TBPar res = new TBPar(this.size()+1);
    for (int i = 0; i < this.size(); i++) {
      res.addElement(this.exprAt(i));
    }
    res.addElement(ln);
    return res;
  }

  /* This method appends two expressions to the tail of Par.  */
  public final TBPar append(LiveExprNode ln1, LiveExprNode ln2) {
    TBPar res = new TBPar(this.size()+2);
    for (int i = 0; i < this.size(); i++) {
      res.addElement(this.exprAt(i));
    }
    res.addElement(ln1);
    res.addElement(ln2);
    return res;
  }

  /**
   * The methods alphaTriples and betaTriples, given a positive
   * closure, figure out the alpha and beta triples. The way the
   * algorithm works, by the time we extract triples, it should
   * already have been positively closed.  All junctions must have
   * been binarified at this stage by makeBinary, otherwise it may
   * give the wrong answer and crash.
   */
  public final Vect alphaTriples() {
    Vect ts = new Vect();
    for (int i = 0; i < this.size(); i++) {
      LiveExprNode ln = this.exprAt(i);
      if (ln instanceof LNAll) {
	ts.addElement(new TBTriple(ln, ((LNAll)ln).getBody(), new LNNext(ln)));
      }
      else if (ln instanceof LNConj) {
	LNConj lnc = (LNConj)ln; 
	ts.addElement(new TBTriple(lnc, lnc.getBody(0), lnc.getBody(1)));
      }
    }
    return ts;
  }

  public final Vect betaTriples() {
    Vect ts = new Vect();
    for (int i = 0; i < this.size(); i++) {
      LiveExprNode ln = this.exprAt(i);
      if (ln instanceof LNEven) {
	ts.addElement(new TBTriple(ln, ((LNEven)ln).getBody(), new LNNext(ln)));
      }
      else if (ln instanceof LNDisj) {
	LNDisj lnd = (LNDisj)ln; 
	ts.addElement(new TBTriple(lnd, lnd.getBody(0), lnd.getBody(1)));
      }
    }
    return ts;
  }

  /**
   * The method isLocallyConsistent determines whether a list of state
   * predicates is locally consistent.
   */
  public final boolean isLocallyConsistent() {
    // First put the elements into positive or negative bin
    TBPar pos = new TBPar(this.size()); 
    TBPar neg = new TBPar(this.size());
    for (int i = 0; i < this.size(); i++) {
      LiveExprNode ln = this.exprAt(i);
      if (ln instanceof LNState) {
	pos.addElement(ln);
      }
      else if (ln instanceof LNNeg) {
	LiveExprNode body = ((LNNeg)ln).getBody();
	if (body instanceof LNState) {
	  neg.addElement(body);
	}
      }
    }
    // If any positive is in the negative bin, that's a clash.
    for (int i = 0; i < pos.size(); i++) { 
      if (neg.member(pos.exprAt(i))) return false;
    }
    return true;
  }

  /**
   * This method, given a list of terms, returns all those terms and
   * subterms that are positive (i.e. whose major operator is not a
   * negation).  There can not be LNActs in the expression.
   */
  public final TBPar positiveClosure() {
    // tps is the queue of terms to be processed.
    TBPar tps = new TBPar(this.size()*2);
    for (int i = 0; i < this.size(); i++) {
      tps.addElement(this.elementAt(i));
    }
    TBPar res = new TBPar(this.size()*2);
    while (tps.size() > 0) {
      LiveExprNode ln = tps.exprAt(tps.size()-1);
      tps.removeLastElement();
      if (ln instanceof LNNeg) {
	tps.addElement(((LNNeg)ln).getBody());
      }
      else if (ln instanceof LNNext) {
	res.addElement(ln);
	tps.addElement(((LNNext)ln).getBody());
      }
      else if (ln instanceof LNEven) {
	res.addElement(ln);
	res.addElement(new LNNext(ln));
	tps.addElement(((LNEven)ln).getBody());
      }
      else if (ln instanceof LNAll) {
	res.addElement(ln);
	res.addElement(new LNNext(ln));
	tps.addElement(((LNAll)ln).getBody());
      }
      else if (ln instanceof LNConj) {
	LNConj lnc = (LNConj)ln;
        for (int i = 0; i < lnc.getCount(); i++) {
	  tps.addElement(lnc.getBody(i));
	}
        res.addElement(ln);
      }
      else if (ln instanceof LNDisj) { 
	LNDisj lnd = (LNDisj)ln;
        for (int i = 0; i < lnd.getCount(); i++) {
	  tps.addElement(lnd.getBody(i));
	}
        res.addElement(ln);
      }
      else if (ln instanceof LNState) {
	res.addElement(ln);
      }
      else if (ln instanceof LNBool) {
	res.addElement(ln);
      }
      else 
      {
          Assert.fail(EC.TLC_LIVE_ENCOUNTERED_ACTIONS);
      }
    }
    return res;
  }

  /**
   * This method returns a list of implied successors of a given
   * particle.
   */
  public final TBPar impliedSuccessors() {
    TBPar successors = new TBPar(this.size());
    for (int i = 0; i < this.size(); i++) { 
      LiveExprNode ln = this.exprAt(i);
      if (ln instanceof LNNext) {
	successors.addElement(((LNNext)ln).getBody());
      }
    }
    return successors;
  }

  /**
   * This methods returns true iff this particle fulfills the promise.
   */
  public final boolean isFulfilling(LNEven promise) {
    return !this.member(promise) || this.member(promise.getBody());
  }

  public final void toString(StringBuffer sb, String padding) {
    sb.append("{");
    String padding1 = padding + " ";
    if (this.size() != 0) {
      ((LiveExprNode)this.elementAt(0)).toString(sb, padding1);
    }
    for (int i = 1; i < this.size(); i++) {
      sb.append(",\n");
      sb.append(padding1);
      ((LiveExprNode)this.elementAt(i)).toString(sb, padding1);
    }
    sb.append("}");
  }
  
  public final String toString() {
    StringBuffer sb = new StringBuffer();
    this.toString(sb, "");
    return sb.toString();
  }
  
}
