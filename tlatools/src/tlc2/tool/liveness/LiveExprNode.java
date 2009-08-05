// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:18 PST by lamport
//      modified on Sun Aug  5 00:00:56 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.Vect;
import util.WrongInvocationException;

/**
 * LNConj - a conjunction. (contains list of conjuncts)
 * LNDisj - a disjunction. (contains list of disjuncts)
 * LNAll - Allways: []e
 * LNEven - Eventually: <>e
 * LNNeg - Negation: -e
 * LNState - State predicate. Concrete types: LNStateAST, LNStateEnabled
 * LNAction - Transition predicate.
 * LNNext - next. ()e. Only used for tableau construction. Not part of TLA
 * 
 * LNState and LNAction have tags. When constructing the tableau, we will
 * have to check whether two primitives are equal to each other, to
 * distinguish atoms.  We could do it just by checking the object
 * pointers to the Act and State ASTNodes.  But to make it absolutely
 * explicit, I will use integer tags. These are initialized to
 * distinct values immediately before tableau construction, used
 * during tableau construction, and not used any more.
 * 
 * There's a little bit of a hierarchy for the LNState.  That's
 * because LNStateAST (which has just an ASTNode for the state
 * predicate) must be evaluated differently from LNStateEnabled (which
 * has ENABLED ast in it)
 * 
 * We are going to end up evaluating LNState and LNAction when we come
 * to construct the tableau graph. That's for the EAs, the EAs, and for
 * local consistency.  Therefore LNState and LNAction have appropriate
 * eval functions.
 **/

abstract class LiveExprNode {
  /**
   * getLevel() = 0 --> constant
   * getLevel() = 1 --> state expression
   * getLevel() = 2 --> action expression
   * getLevel() = 3 --> temporal expression
   */
  public abstract int getLevel();

  /* Returns true iff the expression contains action. */
  public abstract boolean containAction();

  public abstract boolean eval(Tool tool, TLCState s1, TLCState s2);

  /* The string representation. */
  public final String toString() {
    StringBuffer sb = new StringBuffer();
    this.toString(sb, "");
    return sb.toString();
  }

  public abstract void toString(StringBuffer sb, String padding);
  
  /**
   * This method returns true or false for whether two LiveExprNodes
   * are syntactically equal.
   */
  public final boolean equals(LiveExprNode exp) {
    if (this instanceof LNNeg) {
      return ((exp instanceof LNNeg) &&
	      ((LNNeg)this).getBody().equals(((LNNeg)exp).getBody()));
    }
    if (this instanceof LNNext) {
      return ((exp instanceof LNNext) &&
	      ((LNNext)this).getBody().equals(((LNNext)exp).getBody()));
    }
    if (this instanceof LNEven) {
      return ((exp instanceof LNEven) &&
	      ((LNEven)this).getBody().equals(((LNEven)exp).getBody()));
    }
    if (this instanceof LNAll) {
      return ((exp instanceof LNAll) &&
	      ((LNAll)this).getBody().equals(((LNAll)exp).getBody()));
    }
    if (this instanceof LNState) {
      return ((exp instanceof LNState) &&
	      ((LNState)this).getTag() == ((LNState)exp).getTag());
    }
    if (this instanceof LNAction) {
      return ((exp instanceof LNAction) &&
	      ((LNAction)this).getTag() == ((LNAction)exp).getTag());
    }
    if (this instanceof LNConj) {
      if (!(exp instanceof LNConj)) return false;
      LNConj exp1 = (LNConj)this;
      LNConj exp2 = (LNConj)exp;
      if (exp1.getCount() != exp2.getCount()) return false;
      for (int i = 0; i < exp1.getCount(); i++) {
	if (!exp1.getBody(i).equals(exp2.getBody(i))) return false;
      }
      return true;
    }
    if (this instanceof LNDisj) {
      if (!(exp instanceof LNDisj)) return false;
      LNDisj exp1 = (LNDisj)this;
      LNDisj exp2 = (LNDisj)exp;
      if (exp1.getCount() != exp2.getCount()) return false;
      for (int i = 0; i < exp1.getCount(); i++) {
	if (!exp1.getBody(i).equals(exp2.getBody(i))) return false;
      }
      return true;
    }
    return (exp instanceof LNBool) && (((LNBool)this).b == ((LNBool)exp).b);
  }

  /* Return A if this expression is of form []<>A.  */
  public final LiveExprNode getAEBody() {
    if (this instanceof LNAll) {
      LiveExprNode allBody = ((LNAll)this).getBody();
      if (allBody instanceof LNEven) {
	return ((LNEven)allBody).getBody();
      }
    }
    return null;
  }
  
  /* Return A if this expression is of form <>[]A.  */
  public final LiveExprNode getEABody() {
    if (this instanceof LNEven) {
      LiveExprNode evenBody = ((LNEven)this).getBody();
      if (evenBody instanceof LNAll) {
	return ((LNAll)evenBody).getBody();
      }
    }
    return null;
  }

  /**
   * Return true if this expression is a general temporal formula
   * containing no []<>A or <>[]A.
   */
  public final boolean isGeneralTF() {
    if (this instanceof LNAll) {
      LiveExprNode allBody = ((LNAll)this).getBody();
      if (allBody instanceof LNEven) return false;
    }
    else if (this instanceof LNEven) {
      LiveExprNode evenBody = ((LNEven)this).getBody();
      if (evenBody instanceof LNAll) return false;
    }
    else if (this instanceof LNDisj) {
      LNDisj lnd = (LNDisj)this;
      for (int i = 0; i < lnd.getCount(); i++) {
	if (!lnd.getBody(i).isGeneralTF()) return false;
      }
    }
    else if (this instanceof LNConj) {
      LNConj lnc = (LNConj)this;
      for (int i = 0; i < lnc.getCount(); i++) {
	if (!lnc.getBody(i).isGeneralTF()) return false;
      }
    }
    else if (this instanceof LNNeg) {
      return ((LNNeg)this).getBody().isGeneralTF();
    }
    return true;
  }
  
  /* This method pushes a negation all the way down to the atoms. */
  public final LiveExprNode pushNeg() {
    if (this instanceof LNNeg) {
      return ((LNNeg)this).getBody();
    }
    if (this instanceof LNAll) {
      return new LNEven(((LNAll)this).getBody().pushNeg());
    }
    if (this instanceof LNEven) {
      return new LNAll(((LNEven)this).getBody().pushNeg());
    }
    if (this instanceof LNDisj) {
      LNDisj lnd = (LNDisj)this;
      LNConj lnc = new LNConj(lnd.getCount());
      for (int i = 0; i < lnd.getCount(); i++) {
	lnc.addConj(lnd.getBody(i).pushNeg());
      }
      return lnc;
    }
    if (this instanceof LNConj) {
      LNConj lnc = (LNConj)this;
      LNDisj lnd = new LNDisj(lnc.getCount());
      for (int i = 0; i < lnc.getCount(); i++) {
	lnd.addDisj(lnc.getBody(i).pushNeg());
      }
      return lnd;
    }
    if (this instanceof LNBool) {
      return new LNBool(!((LNBool)this).b);
    }
    // for the remaining types, simply negate:
    return new LNNeg(this);
  }

  /**
   * This method pushes a negation all the way down to the atoms.
   * It is currently not used.
   */
  public final LiveExprNode pushNeg(boolean hasNeg) {
    if (this instanceof LNNeg) {
      LiveExprNode lexpr = ((LNNeg)this).getBody();
      return lexpr.pushNeg(!hasNeg);
    }
    else if (this instanceof LNAll) {
      if (hasNeg) {
	return new LNEven(((LNAll)this).getBody().pushNeg(true));
      }
      else {
	return new LNAll(((LNAll)this).getBody().pushNeg(false));
      }
    }
    else if (this instanceof LNEven) {
      if (hasNeg) {
	return new LNAll(((LNEven)this).getBody().pushNeg(true));
      }
      else {
	return new LNEven(((LNEven)this).getBody().pushNeg(false));
      }
    }
    else if (this instanceof LNDisj) {
      LNDisj lnd = (LNDisj)this;
      if (hasNeg) {
	LNConj lnc = new LNConj(lnd.getCount());
	for (int i = 0; i < lnd.getCount(); i++) {
	  lnc.addConj(lnd.getBody(i).pushNeg(true));
	}
	return lnc;
      }
      else {
	LNDisj lnd1 = new LNDisj(lnd.getCount());
	for (int i = 0; i < lnd.getCount(); i++) {
	  lnd1.addDisj(lnd.getBody(i).pushNeg(false));
	}
	return lnd1;
      }
    }
    else if (this instanceof LNConj) {
      LNConj lnc = (LNConj)this;
      if (hasNeg) {
	LNDisj lnd = new LNDisj(lnc.getCount());
	for (int i = 0; i < lnc.getCount(); i++) {
	  lnd.addDisj(lnc.getBody(i).pushNeg(true));
	}
	return lnd;
      }
      else {
	LNConj lnc1 = new LNConj(lnc.getCount());
	for (int i = 0; i < lnc.getCount(); i++) {
	  lnc1.addConj(lnc.getBody(i).pushNeg(false));
	}
	return lnc1;
      }
    }
    // for the remaining types, negate when needed:
    else if (hasNeg) {
      if (this instanceof LNBool) {
	return new LNBool(!((LNBool)this).b);
      }
      else {
	return new LNNeg(this);
      }
    }
    return this;
  }

  /**
   * The method simplify does some simple simplifications before
   * starting any real work. It will get rid of any boolean constants
   * (of type LNBool).
   */
  public final LiveExprNode simplify() {
    if (this instanceof LNNeg) {
      LiveExprNode body1 = ((LNNeg)this).getBody().simplify();
      if (body1 instanceof LNBool) {
	return new LNBool(!((LNBool)body1).b);
      }
      return new LNNeg(body1);
    }
    if (this instanceof LNAll) {
      LiveExprNode body1 = ((LNAll)this).getBody().simplify();
      if (body1 instanceof LNAll) {
	body1 = ((LNAll)body1).getBody();
      }
      return new LNAll(body1);
    }
    if (this instanceof LNEven) {
      LiveExprNode body1 = ((LNEven)this).getBody().simplify();
      if (body1 instanceof LNEven) {
	body1 = ((LNEven)body1).getBody();
      }
      return new LNEven(body1);
    }
    if (this instanceof LNDisj) {
      LNDisj lnd = (LNDisj)this;
      LNDisj lnd1 = new LNDisj(lnd.getCount());
      for (int i = 0; i < lnd.getCount(); i++) {
	LiveExprNode elem = lnd.getBody(i).simplify();
	if (elem instanceof LNBool) {
	  if (((LNBool)elem).b) return LNBool.TRUE;
	}
	else {
	  lnd1.addDisj(elem);
	}
      }
      if (lnd1.getCount() == 0) return LNBool.FALSE;
      if (lnd1.getCount() == 1) return lnd1.getBody(0);
      return lnd1;
    }
    if (this instanceof LNConj) {
      LNConj lnc = (LNConj)this;
      LNConj lnc1 = new LNConj(lnc.getCount());
      for (int i = 0; i < lnc.getCount(); i++) {
	LiveExprNode elem = lnc.getBody(i).simplify();
	if (elem instanceof LNBool) {
	  if (!((LNBool)elem).b) return LNBool.FALSE;
	}
	else {
	  lnc1.addConj(elem);
	}
      }
      if (lnc1.getCount() == 0) return LNBool.TRUE;
      if (lnc1.getCount() == 1) return lnc1.getBody(0);
      return lnc1;
    }
    // for the remaining types, simply negate:
    return this;
  }
  
  /**
   * The method toDNF turns a LiveExprNode into disjunctive normal
   * form.
   */
  public final LiveExprNode toDNF() {
    if (this instanceof LNNeg) {
      LiveExprNode body = ((LNNeg)this).getBody();
      if ((body instanceof LNState) || (body instanceof LNAction)) {
	return this;
      }
      return body.pushNeg().toDNF();
    }
    else if (this instanceof LNConj) {
      LNConj conj = (LNConj)this;
      int count = conj.getCount();
      LiveExprNode[] temp = new LiveExprNode[count];
      for (int i = 0; i < count; i++) {
	temp[i] = conj.getBody(i).toDNF();
      }

      // We now construct the cross product:
      Vect nes = new Vect(count);
      int total = 1;
      for (int i = 0; i < count; i++) {
	LiveExprNode elem = temp[i];
	if (elem instanceof LNDisj) {
	  nes.addElement(elem);
	  total *= ((LNDisj)elem).getCount();
	}
	else if (elem instanceof LNConj) {
	  // Flatten when elem is also a LNConj:
	  LNConj elem1 = (LNConj)elem;
	  int count1 = elem1.getCount();
	  for (int j = 0; j < count1; j++) {
	    nes.addElement(elem1.getBody(j));
	  }
	}
	else {
	  nes.addElement(elem);
	}
      }

      if (total == 1) {
	return new LNConj(nes);
      }
      int nesSize = nes.size();
      Vect res = new Vect(total);
      for (int i = 0; i < total; i++) {
	res.addElement(new LNConj(nesSize));
      }
      int num = 1;
      int rCount = total;
      for (int i = 0; i < nesSize; i++) {
	LiveExprNode ln = (LiveExprNode)nes.elementAt(i);
	if (ln instanceof LNDisj) {
	  LNDisj disj = (LNDisj)ln;
	  rCount = rCount/disj.getCount();
	  int idx = 0;
	  for (int j = 0; j < num; j++) {
	    for (int k = 0; k < disj.getCount(); k++) {
	      LiveExprNode elem = disj.getBody(k);
	      for (int l = 0; l < rCount; l++) {
		((LNConj)res.elementAt(idx++)).addConj(elem);
	      }
	    }
	  }
	  num = num * disj.getCount();
	}
	else {
	  for (int j = 0; j < total; j++) {
	    ((LNConj)res.elementAt(j)).addConj(ln);
	  }
	}
      }
      return new LNDisj(res);
    }
    else if (this instanceof LNDisj) {
      // Apply []<>A1 \/ []<>A2 = []<>(A1 \/ A2) when possible.
      LNDisj disj = (LNDisj)this;
      LNDisj aeRes = new LNDisj(0);
      LNDisj res = new LNDisj(0);
      for (int i = 0; i < disj.getCount(); i++) {
	LiveExprNode elem = disj.getBody(i).toDNF();
	if (elem instanceof LNDisj) {
	  LNDisj disj1 = (LNDisj)elem;
	  for (int j = 0; j < disj1.getCount(); j++) {
	    LiveExprNode elem1 = disj1.getBody(j);
	    LiveExprNode elemBody = elem1.getAEBody();
	    if (elemBody == null) {
	      res.addDisj(elem1);
	    }
	    else {
	      aeRes.addDisj(elemBody);
	    }	    
	  }
	}
	else {
	  LiveExprNode elemBody = elem.getAEBody();
	  if (elemBody == null) {
	    res.addDisj(elem);
	  }
	  else {
	    aeRes.addDisj(elemBody);
	  }
	}
      }
      // Add aeRes to res before returning.
      if (aeRes.getCount() == 1) {
	res.addDisj(new LNAll(new LNEven(aeRes.getBody(0))));
      }
      else if (aeRes.getCount() > 1) {
	res.addDisj(new LNAll(new LNEven(aeRes)));
      }	
      return res;
    }
    // For the remaining types, there is nothing to do:
    return this;
  }

  /**
   * This method eliminates (flattens) singleton conjunctions and
   * disjunctions. For example, /\[single-thing] is rewritten to
   * single-thing. Note: With the current version of toDNF, there is
   * probably no need for calling this method.
   */
  public final LiveExprNode flattenSingleJunctions() {
    if (this instanceof LNConj) {
      LNConj lnc = (LNConj)this;
      if (lnc.getCount() == 1) {
	return lnc.getBody(0).flattenSingleJunctions();
      }
      LNConj lnc2 = new LNConj(lnc.getCount());
      for (int i = 0; i < lnc.getCount(); i++) {
	lnc2.addConj(lnc.getBody(i).flattenSingleJunctions());
      }
      return lnc2;
    }
    if (this instanceof LNDisj) {
      LNDisj lnd = (LNDisj)this;
      if (lnd.getCount() == 1) {
	return lnd.getBody(0).flattenSingleJunctions();
      }
      LNDisj lnd2 = new LNDisj(lnd.getCount());
      for (int i = 0; i < lnd.getCount(); i++) {
	lnd2.addDisj(lnd.getBody(i).flattenSingleJunctions());
      }
      return lnd2;
    }
    if (this instanceof LNNeg) {
      LiveExprNode ln1 = ((LNNeg)this).getBody();
      if (ln1 instanceof LNNeg) {
	return ((LNNeg)ln1).getBody().flattenSingleJunctions();
      }
      return new LNNeg(ln1.flattenSingleJunctions());
    }
    if (this instanceof LNNext) {
      return new LNNext(((LNNext)this).getBody().flattenSingleJunctions());
    }
    if (this instanceof LNEven) {
      return new LNEven(((LNEven)this).getBody().flattenSingleJunctions());
    }
    if (this instanceof LNAll) {
      return new LNAll(((LNAll)this).getBody().flattenSingleJunctions());
    }
    // Finally, for the remaining types, there is nothing to do:
    return this;
  }

  /**
   * This method makes all conjunctions and disjunctions binary. This
   * is for tableau 'triple' construction. We'll do a recursive thing
   * to balance the binary trees. Note that there can be no LNActions.
   */
  public final LiveExprNode makeBinary() {
    if (this instanceof LNNeg) {
      return new LNNeg(((LNNeg)this).getBody().makeBinary());
    }
    else if (this instanceof LNNext) {
      return new LNNext(((LNNext)this).getBody().makeBinary());
    }
    else if (this instanceof LNEven) {
      return new LNEven(((LNEven)this).getBody().makeBinary());
    }
    else if (this instanceof LNAll) {
      return new LNAll(((LNAll)this).getBody().makeBinary());
    }
    else if (this instanceof LNConj) {
      LNConj lnc = (LNConj)this;
      if (lnc.getCount() == 1) return lnc.getBody(0).makeBinary();
      int mid = lnc.getCount()/2;
      LNConj left = new LNConj(0);
      LNConj right = new LNConj(0);
      for (int i = 0; i < lnc.getCount(); i++) {
	if (i < mid)
	  left.addConj(lnc.getBody(i));
	else
	  right.addConj(lnc.getBody(i));
      }
      return new LNConj(left.makeBinary(), right.makeBinary());
    }
    else if (this instanceof LNDisj) {
      LNDisj lnd = (LNDisj)this;
      if (lnd.getCount() == 1) {
	return lnd.getBody(0).makeBinary();
      }
      int mid = lnd.getCount()/2;
      LNDisj left = new LNDisj(0);
      LNDisj right = new LNDisj(0);
      for (int i = 0; i < lnd.getCount(); i++) {
	if (i < mid) {
	  left.addDisj(lnd.getBody(i));
	}
	else {
	  right.addDisj(lnd.getBody(i));
	}
      }
      return new LNDisj(left.makeBinary(), right.makeBinary());
    }
    else if ((this instanceof LNState) ||
	     (this instanceof LNBool)) {
      return this;
    }
    // We do not deal with actions:
    throw new WrongInvocationException("LiveExprNode.makeBinary: TLC encounters actions.");
  }

  /**
   * TagExpr tags all Act and State subexpressions in an expression.
   * It returns the maximum tag used so that the caller can proceed
   * with other tags in its depth-first traversal.
   */
  public int tagExpr(int tag) {
    if (this instanceof LNAction) {
      ((LNAction)this).setTag(tag);
      return tag+1;
    }
    if (this instanceof LNState) {
      ((LNState)this).setTag(tag);
      return tag+1;
    }
    if (this instanceof LNNeg) {
      return ((LNNeg)this).getBody().tagExpr(tag);
    }
    if (this instanceof LNAll) {
      return ((LNAll)this).getBody().tagExpr(tag);
    }
    if (this instanceof LNEven) {
      return ((LNEven)this).getBody().tagExpr(tag);
    }
    if (this instanceof LNConj) {
      LNConj lnc = (LNConj)this;
      for (int i = 0; i < lnc.getCount(); i++) {
	tag = lnc.getBody(i).tagExpr(tag);
      }
      return tag;
    }
    if (this instanceof LNDisj) {
      LNDisj lnd = (LNDisj)this;
      for (int i = 0; i < lnd.getCount(); i++) {
	tag = lnd.getBody(i).tagExpr(tag);
      }
      return tag;
    }
    return tag;
  }

  /**
   * The method extractPromises, given a formula, returns all the
   * promises in its closure.  All promises are in the form <>p. (We
   * assume that we have pushed all negations inside. So, there are no
   * -[]ps.)  The closure of a formula says: for all subformulas of p,
   * they are also in the closure. And some other rules, none of which
   * have the possibility of creating a promise!  So we only need
   * look at subformulas of p.
   */
  public final void extractPromises(TBPar promises) {
    if (this instanceof LNNeg) {
      ((LNNeg)this).getBody().extractPromises(promises);
    }
    else if (this instanceof LNNext) {
      ((LNNext)this).getBody().extractPromises(promises);
    }
    else if (this instanceof LNEven) {
      LNEven lne = (LNEven)this;
      if (!promises.member(lne)) {
	promises.addElement(lne);
      }
      lne.getBody().extractPromises(promises);
    }
    else if (this instanceof LNAll) {
      ((LNAll)this).getBody().extractPromises(promises);
    }
    else if (this instanceof LNConj) {
      LNConj lnc = (LNConj)this;
      lnc.getBody(0).extractPromises(promises);
      lnc.getBody(1).extractPromises(promises);
    }
    else if (this instanceof LNDisj) {
      LNDisj lnd = (LNDisj)this;
      lnd.getBody(0).extractPromises(promises);
      lnd.getBody(1).extractPromises(promises);
    }
    // Finally, for the remaining kinds, there is nothing to do.
    return;
  }

}
