// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;

import tla2sany.explorer.ExploreNode;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;

public class Subst implements LevelConstants, ASTConstants, ExploreNode {

  /** 
   * This class represents a single substitution of the form
   * op <- expr such as appears in module instantiations.
   */
  private OpDeclNode       op;
  private ExprOrOpArgNode  expr;
  private TreeNode         exprSTN;
  private boolean          implicit;

  /* Constructors */
  public Subst(OpDeclNode odn, ExprOrOpArgNode exp, TreeNode exSTN, boolean imp) {
    this.op       = odn;
    this.expr     = exp;
    this.exprSTN  = exSTN;
    this.implicit = imp;
  }

  public final OpDeclNode getOp() { return this.op; }

  public final void setOp(OpDeclNode opd) { this.op = opd; }

  public final ExprOrOpArgNode getExpr() { return this.expr; }

  public final void setExpr(ExprOrOpArgNode exp, boolean imp) {
    this.expr = exp;
    this.implicit = imp;
  }

  public final TreeNode getExprSTN() { return this.exprSTN; }

  public final void setExprSTN(TreeNode stn) { this.exprSTN = stn; }

  public final boolean isImplicit() { return this.implicit; }

  public static ExprOrOpArgNode getSub(Object param, Subst[] subs) {
    for (int i = 0; i < subs.length; i++) {
      if (subs[i].getOp() == param) {
	return subs[i].getExpr();
      }
    }
    return null;
  }

  public static HashSet paramSet(Object param, Subst[] subs) {
    /***********************************************************************
    * If subs[i] is of the form `parm <- expr', then it returns the        *
    * expr.levelParams.  Otherwise, it returns the HashSet containing      *
    * only param.                                                          *
    *                                                                      *
    * This should only be called after level checking has been called on   *
    * all subs[i].getExpr().                                               *
    ***********************************************************************/
    int idx;
    for (idx = 0; idx < subs.length; idx++) {
      if (subs[idx].getOp() == param) break;
    }
    if (idx < subs.length) {
      return subs[idx].getExpr().getLevelParams();
    }

    HashSet res = new HashSet();
    res.add(param);
    return res;
  }

  public static HashSet allParamSet(Object param, Subst[] subs) {
    /***********************************************************************
    * This is exactly like paramSet, except it returns the allParams       *
    * HashSet instead of levelParams.                                      *
    ***********************************************************************/
    int idx;
    for (idx = 0; idx < subs.length; idx++) {
      if (subs[idx].getOp() == param) break;
    }
    if (idx < subs.length) {
      return subs[idx].getExpr().getAllParams();
    }

    HashSet res = new HashSet();
    res.add(param);
    return res;
  }

  public static SetOfLevelConstraints getSubLCSet(LevelNode body,
						  Subst[] subs,
						  boolean isConstant,
                                                  int itr) {
    /***********************************************************************
    * This should only be called after level checking has been called on   *
    * body and on all subs[i].getExpr().  The itr argument is the          *
    * iteration number for calling levelCheck.                             *
    ***********************************************************************/
    SetOfLevelConstraints res = new SetOfLevelConstraints();
    SetOfLevelConstraints lcSet = body.getLevelConstraints();
    Iterator iter = lcSet.keySet().iterator();
    while (iter.hasNext()) {
      SymbolNode param = (SymbolNode)iter.next();
      Object plevel = lcSet.get(param);
      if (!isConstant) {
	if (param.getKind() == ConstantDeclKind) {
	  plevel = Levels[ConstantLevel];
	}
	else if (param.getKind() == VariableDeclKind) {
	  plevel = Levels[VariableLevel];
	}
      }
      Iterator iter1 = paramSet(param, subs).iterator();
      while (iter1.hasNext()) {
	res.put(iter1.next(), plevel);
      }
    }
    HashSet alpSet = body.getArgLevelParams();
    iter = alpSet.iterator();
    while (iter.hasNext()) {
      ArgLevelParam alp = (ArgLevelParam)iter.next();
      OpArgNode sub = (OpArgNode)getSub(alp.op, subs);
      if (sub != null &&
	  sub.getOp() instanceof OpDefNode) {
	OpDefNode subDef = (OpDefNode)sub.getOp();
        subDef.levelCheck(itr);
          /*****************************************************************
          * The call of getMaxLevel should be made only to a node that     *
          * has been level checked.  But this node has come from looking   *
          * up an operator in some hash table, and there's no way of       *
          * knowing if it's been level checked.  So, we have to level      *
          * check it first, which is why we need the iteration number      *
          * argument of this method.                                       *
          *****************************************************************/
	Integer mlevel = new Integer(subDef.getMaxLevel(alp.i)); 
	Iterator iter1 = paramSet(alp.param, subs).iterator();
	while (iter1.hasNext()) {
	  res.put(iter1.next(), mlevel);
	}
      }
    }
    return res;
  }

  public static SetOfArgLevelConstraints getSubALCSet(
                  LevelNode body, Subst[] subs, int itr) {
    /***********************************************************************
    * Can be called only after levelCheck has been called on body.  The    *
    * argument itr is the argument for calling levelCheck.                 *
    ***********************************************************************/
    SetOfArgLevelConstraints res = new SetOfArgLevelConstraints();
    SetOfArgLevelConstraints alcSet = body.getArgLevelConstraints();
    Iterator iter = alcSet.keySet().iterator();
    while (iter.hasNext()) {
      ParamAndPosition pap = (ParamAndPosition)iter.next();
      Object plevel = alcSet.get(pap);
      ExprOrOpArgNode sub = getSub(pap.param, subs);
      if (sub == null) {
	res.put(pap, plevel);
      }
      else {
	SymbolNode subOp = ((OpArgNode)sub).getOp();
	if (subOp.isParam()) {
	  pap = new ParamAndPosition(subOp, pap.position);
	  res.put(pap, plevel);
	}
      }
    }
    HashSet alpSet = body.getArgLevelParams();
    iter = alpSet.iterator();
    while (iter.hasNext()) {
      ArgLevelParam alp = (ArgLevelParam)iter.next();
      ExprOrOpArgNode subParam = getSub(alp.param, subs);
      if (subParam != null) {
	ExprOrOpArgNode subOp = getSub(alp.op, subs);
	SymbolNode op = (subOp == null) ? alp.op : ((OpArgNode)subOp).getOp();
	if (op.isParam()) {
	  ParamAndPosition pap = new ParamAndPosition(op, alp.i);
          subParam.levelCheck(itr) ;
            /***************************************************************
            * Must invoke levelCheck before invoking getLevel              *
            ***************************************************************/
	  Integer subLevel = new Integer(subParam.getLevel());
	  res.put(pap, subLevel);
	}
      }
    }
    return res;
  }

  public static HashSet getSubALPSet(LevelNode body, Subst[] subs) {
    /***********************************************************************
    * This should only be called after level checking has been called on   *
    * body and on all subs[i].getExpr().                                   *
    ***********************************************************************/
    HashSet res = new HashSet();
    HashSet alpSet = body.getArgLevelParams();
    Iterator iter = alpSet.iterator();
    while (iter.hasNext()) {
      ArgLevelParam alp = (ArgLevelParam)iter.next();
      ExprOrOpArgNode sub = getSub(alp.op, subs);
      if (sub == null) {
	res.add(alp);
      }
      else {
	SymbolNode subOp = ((OpArgNode)sub).getOp();
	if (subOp.isParam()) {
	  Iterator iter1 = paramSet(alp.param, subs).iterator();
	  while (iter1.hasNext()) {
	    res.add(new ArgLevelParam(subOp, alp.i, (SymbolNode)iter1.next()));
	  }
	}
      }
    }
    return res;
  }
  
  public final String levelDataToString() { return "Dummy level string"; }

  public final void walkGraph(Hashtable semNodesTable) {
    if (op != null) op.walkGraph(semNodesTable);
    if (expr != null) expr.walkGraph(semNodesTable);
  }

  public final String toString(int depth) {
    return "\nOp: " + Strings.indent(2,(op!=null ? op.toString(depth-1) : 
                                           "<null>" )) + 
           "\nExpr: " + Strings.indent(2,(expr!=null ? expr.toString(depth-1) : "<null>"));
  }

}
