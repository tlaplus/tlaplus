// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:18 PST by lamport
//      modified on Fri Jan  4 00:31:02 PST 2002 by yuanyu

package tlc2.tool.liveness;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.Action;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.ContextEnumerator;
import tlc2.tool.EvalControl;
import tlc2.tool.Spec;
import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.tool.ToolGlobals;
import tlc2.util.Context;
import tlc2.util.Vect;
import tlc2.value.BoolValue;
import tlc2.value.FcnLambdaValue;
import tlc2.value.Value;
import util.Assert;

public class Liveness implements ToolGlobals, ASTConstants {

  private static LiveExprNode astToLive(Tool tool, ExprNode expr,
					Context con, int level) {
    if (level == 0) {
      Value val = tool.eval(expr, con, TLCState.Empty);
      if (!(val instanceof BoolValue)) {
          Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()});
      }
      return (((BoolValue)val).val) ? LNBool.TRUE : LNBool.FALSE;
    }
    else if (level == 1) {
      return new LNStateAST(expr, con);
    }
    else {
      // Assert.check(level == 2);
      return new LNAction(expr, con);
    }
  }
    
  /**
   * The method astToLive converts an ExprNode into a LiveExprNode.
   * o We are passing down a tool and a context as we parse the
   *   expressions recursively.  That's for calling eval().
   * o The method has some restrictions. If you did Predicate([]p),
   *   then we'd need to instantiate the predicate body with []p.
   *   For the moment, we require that arguments to predicates
   *   be computable from its context.
   */
  static LiveExprNode astToLive(Tool tool, ExprNode expr, Context con) {
    switch (expr.getKind()) {
    case OpApplKind:
      {
	OpApplNode expr1 = (OpApplNode)expr;
	return astToLiveAppl(tool, expr1, con);
      }
    case LetInKind:
      {
	LetInNode expr1 = (LetInNode)expr;
	return astToLive(tool, expr1.getBody(), con);
      }
    case SubstInKind:
      {
	SubstInNode expr1 = (SubstInNode)expr;
	Subst[] subs = expr1.getSubsts();
	int slen = subs.length;
	Context con1 = con;
	for (int i = 0; i < slen; i++) {
	  Subst sub = subs[i];
	  con1 = con1.cons(sub.getOp(), tool.getVal(sub.getExpr(), con, false));
	}
	return astToLive(tool, expr1.getBody(), con1);
      }
    default:
      {
	int level = Spec.getLevel(expr, con);
	if (level > 2) {
	    Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, expr.toString());
	}
	return astToLive(tool, expr, con, level);
      }
    }
  }

  private static LiveExprNode astToLiveAppl(Tool tool, OpApplNode expr, Context con) {
    ExprOrOpArgNode[] args = expr.getArgs();
    int alen = args.length;
    SymbolNode opNode = expr.getOperator();
    int opcode = BuiltInOPs.getOpCode(opNode.getName());

    if (opcode == 0) {
      // This is a user-defined operator with one exception: it may
      // be substed by a builtin operator.  This special case is handled
      // by checking if the lookup returns a OpDef with opcode = 0.
      Object val = tool.lookup(opNode, con, false);
      
      if (val instanceof OpDefNode) {
	OpDefNode opDef = (OpDefNode)val;
	opcode = BuiltInOPs.getOpCode(opDef.getName());	
	if (opcode == 0) {
	  try {
	    FormalParamNode[] formals = opDef.getParams();	  
	    Context con1 = con;
	    for (int i = 0; i < alen; i++) {
	      Value argVal = tool.eval(args[i], con, TLCState.Empty);
	      con1 = con1.cons(formals[i], argVal);
	    }
	    LiveExprNode res = astToLive(tool, opDef.getBody(), con1);
	    int level = res.getLevel();
	    if (level > 2) return res;
	    return astToLive(tool, expr, con, level);
	  }
	  catch (Exception e) { /*SKIP*/ }
	}
      }
      else if (val instanceof BoolValue) {
	return (((BoolValue)val).val) ? LNBool.TRUE : LNBool.FALSE;
      }

      if (opcode == 0) {
	int level = Spec.getLevel(expr, con);
	if (level > 2) 
	{
	    Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, expr.toString());
	}
	return astToLive(tool, expr, con, level);
      }
    }
    
    switch (opcode) {
    case OPCODE_be:     // BoundedExists
      {
	ExprNode body = (ExprNode)args[0];
	try {
	  ContextEnumerator Enum =
	    tool.contexts(expr, con, TLCState.Empty, TLCState.Empty, EvalControl.Clear);
	  Context con1;
	  LNDisj res = new LNDisj(0);
	  while ((con1 = Enum.nextElement()) != null) {
	    LiveExprNode kid = astToLive(tool, body, con1);
	    res.addDisj(kid);
	  }
	  int level = res.getLevel();
	  if (level > 2) return res;
	  return astToLive(tool, expr, con, level);
	}
	catch (Exception e) {
	  // Assert.printStack(e);
	  int level = Spec.getLevel(expr, con);
	  if (level > 2) {
	      Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, expr.toString());;
	  }
	  return astToLive(tool, expr, con, level);
	}	
      }
    case OPCODE_bf:     // BoundedForall
      {
	ExprNode body = (ExprNode)args[0];
	try {
	  ContextEnumerator Enum =
	    tool.contexts(expr, con, TLCState.Empty, TLCState.Empty, EvalControl.Clear);
	  Context con1;
	  LNConj res = new LNConj(0);
	  while ((con1 = Enum.nextElement()) != null) {
	    LiveExprNode kid = astToLive(tool, body, con1);
	    res.addConj(kid);
	  }
	  int level = res.getLevel();
	  if (level > 2) return res;
	  return astToLive(tool, expr, con, level);
	}
	catch (Exception e) {
	  // Assert.printStack(e);
	  int level = Spec.getLevel(expr, con);
	  if (level > 2) {
	      Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, expr.toString());;
	  }
	  return astToLive(tool, expr, con, level);
	}
      }
    case OPCODE_cl:     // ConjList
    case OPCODE_land:
      {
	LNConj lnConj = new LNConj(alen);
	for (int i = 0; i < alen; i++) {
	  LiveExprNode kid = astToLive(tool, (ExprNode)args[i], con);
	  lnConj.addConj(kid);
	}
	int level = lnConj.getLevel();
	if (level > 2) return lnConj;
	return astToLive(tool, expr, con, level);
      }
    case OPCODE_dl:     // DisjList
    case OPCODE_lor:
      {
	LNDisj lnDisj = new LNDisj(alen);
	for (int i = 0; i < alen; i++) {
	  LiveExprNode kid = astToLive(tool, (ExprNode)args[i], con);
	  lnDisj.addDisj(kid);
	}
	int level = lnDisj.getLevel();
	if (level > 2) return lnDisj;
	return astToLive(tool, expr, con, level);
      }
    case OPCODE_fa:     // FcnApply
      {
	try {
	  Value fval = tool.eval(args[0], con, TLCState.Empty);
	  if (fval instanceof FcnLambdaValue) {
	    FcnLambdaValue fcn = (FcnLambdaValue)fval;
	    if (fcn.fcnRcd == null) {
	     // this could be a bug, since con1 is created but not
	     // used
	     // SZ Jul 13, 2009: removed to kill the warning
	     // SZ Feb 20, 2009: variable never read locally
	     //  Context con1 = 
	      tool.getFcnContext(fcn, args, con, TLCState.Empty,
						TLCState.Empty, EvalControl.Clear); 
	      return astToLive(tool, (ExprNode)fcn.body, con);
	    }
	  }
	}
	catch (Exception e) { /*SKIP*/ }
	int level = expr.getLevel();
	if (level > 2) {
	    Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, expr.toString());
	}
	return astToLive(tool, expr, con, level);
      }
    case OPCODE_ite:    // IfThenElse
      {
	LiveExprNode guard = astToLive(tool, (ExprNode)args[0], con);
	LiveExprNode e1 = astToLive(tool, (ExprNode)args[1], con);
	LiveExprNode e2 = astToLive(tool, (ExprNode)args[2], con);
	LiveExprNode conj1 = new LNConj(guard, e1);
	LiveExprNode conj2 = new LNConj(new LNNeg(guard), e2);
	LiveExprNode res = new LNDisj(conj1, conj2);
	int level = res.getLevel();
	if (level > 2) return res;
	return astToLive(tool, expr, con, level);
      }
    case OPCODE_lnot:
      {
	LiveExprNode lnArg = astToLive(tool, (ExprNode)args[0], con);
	int level = lnArg.getLevel();
	if (level > 2) return new LNNeg(lnArg);
	return astToLive(tool, expr, con, level);
      }
    case OPCODE_implies:
      {
	LiveExprNode lnLeft = astToLive(tool, (ExprNode)args[0], con);
	LiveExprNode lnRight = astToLive(tool, (ExprNode)args[1], con);
	int level = Math.max(lnLeft.getLevel(), lnRight.getLevel());
	if (level > 2) {
	  return new LNDisj(new LNNeg(lnLeft), lnRight);
	}
	return astToLive(tool, expr, con, level);
      }
    case OPCODE_prime:
      {
	return new LNAction(expr, con);
      }
    case OPCODE_sf:     // SF
      {
	// expand SF_e(A) into <>[]-EN<A>_e \/ []<><A>_e
	ExprNode subs = (ExprNode)args[0];   // the e in SF_e(A)
	ExprNode body = (ExprNode)args[1];   // the A in SF_e(A)
	LiveExprNode en = new LNNeg(new LNStateEnabled(body, con, subs, false));
	LiveExprNode act = new LNAction(body, con, subs, false);
	return new LNDisj(new LNEven(new LNAll(en)), new LNAll(new LNEven(act)));
      }
    case OPCODE_wf:     // WF
      {
	// expand WF_e(A) into []<>(-EN<A>_e \/ <A>_e)
	ExprNode subs = (ExprNode)args[0];   // the e in WF_e(A)
	ExprNode body = (ExprNode)args[1];   // the A in WF_e(A)
	LiveExprNode ln1 = new LNNeg(new LNStateEnabled(body, con, subs, false));
	LiveExprNode ln2 = new LNAction(body, con, subs, false);
	LiveExprNode disj = new LNDisj(ln1, ln2);
	return new LNAll(new LNEven(disj));
      }
    case OPCODE_leadto:
      {
	LiveExprNode lnLeft = astToLive(tool, (ExprNode)args[0], con);
	LiveExprNode lnRight = astToLive(tool, (ExprNode)args[1], con);
	// expand a ~> b into [](-a \/ <>b)
	LNDisj lnd = new LNDisj(new LNNeg(lnLeft), new LNEven(lnRight));
	return new LNAll(lnd);
      }
    case OPCODE_box:
      {
	LiveExprNode lnArg = astToLive(tool, (ExprNode)args[0], con);
	return new LNAll(lnArg);
      }
    case OPCODE_diamond:
      {
	LiveExprNode lnArg = astToLive(tool, (ExprNode)args[0], con);
	return new LNEven(lnArg);
      }
 
    // The following case added by LL on 13 Nov 2009 to handle subexpression names.
    case OPCODE_nop:
     {
         return astToLive(tool, (ExprNode) args[0], con);
     }
    default:
      {
	// We handle all the other built-in operators here.
	int level = Spec.getLevel(expr, con);
	if (level > 2) {
	    Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, expr.toString());;
	}
	return astToLive(tool, expr, con, level);
      }
    }
  }

  /**
   * Given a starting TBGraphNode, constructTableau constructs the
   * tableau for it.  Read MP for details.  It returns a list of
   * all the nodes in the tableau graph.   
   */
  static TBGraph constructTableau(LiveExprNode tf, int idx) {
    TBGraph allnodes = new TBGraph(tf);
    TBPar initTerms = new TBPar(1);
    initTerms.addElement(tf);
    TBParVec pars = particleClosure(initTerms);

    for (int i = 0; i < pars.size(); i++) {
      TBGraphNode gn = new TBGraphNode(pars.parAt(i));
      allnodes.addElement(gn);
    }
    allnodes.setInitCnt(allnodes.size());
    // We now repeatedly compute the outlinks of each node:
    for (int i = 0; i < allnodes.size(); i++) {
      TBGraphNode gnSrc = (TBGraphNode)allnodes.elementAt(i);
      TBPar imps = gnSrc.getPar().impliedSuccessors();
      TBParVec succs = particleClosure(imps);
      for (int j = 0; j < succs.size(); j++) {
	TBPar par = succs.parAt(j);
	TBGraphNode gnDst = findOrCreateNode(allnodes, par);
	gnSrc.nexts.addElement(gnDst);
      }
    }
    // Assign each node in the tableau an index.
    for (int i = 0; i < allnodes.size(); i++) {
      allnodes.getNode(i).index = idx++;
    }
    return allnodes;
  }
  
  /**
   * The method findOrCreateNode, given a list of particles, either
   * finds the particle in that list, or creates a new one and puts it
   * in the list.  If it does create a node, then it also sticks that
   * node into allnodes.
   */
  static TBGraphNode findOrCreateNode(Vect allnodes, TBPar par) {
    for (int i = 0; i < allnodes.size(); i++) {
      TBGraphNode gn = (TBGraphNode)allnodes.elementAt(i);
      if (par.equals(gn.getPar())) return gn;
    }
    TBGraphNode gn = new TBGraphNode(par);
    allnodes.addElement(gn);
    return gn;
  }

  /**
   * The method particleClosure, given a list of terms (initially just
   * a single term), returns a list of all particles containing those
   * terms. It's a recursive tree search.
   */
  static TBParVec particleClosure(TBPar terms) {
    TBPar positive_closure = terms.positiveClosure();
    Vect alphas = positive_closure.alphaTriples();
    Vect betas = positive_closure.betaTriples();
    return particleClosure(terms, alphas, betas);
  }

  static TBParVec particleClosure(TBPar terms, Vect alphas, Vect betas) {
    // if terms is not locally consistent, then terminate.
    if (!terms.isLocallyConsistent()) {
      return new TBParVec(0);
    }
    // if terms is not alpha-closed, then close it.
    // first, try alpha expansion
    TBPar terms1 = terms;
    for (int i = 0; i < terms1.size(); i++) {
      LiveExprNode ln = terms1.exprAt(i);
      LiveExprNode k1 = null, k2 = null;
      if (ln instanceof LNAll) {
	k1 = ((LNAll)ln).getBody();
	k2 = new LNNext(ln);
      }
      else if (ln instanceof LNConj) {
	k1 = ((LNConj)ln).getBody(0);
	k2 = ((LNConj)ln).getBody(1);
      }
      if (k1 != null) {
	if (terms1.member(k1)) {
	  if (!terms1.member(k2)) {
	    terms1 = terms1.append(k2);
	  }
	}
	else if (terms1.member(k2)) {
	  terms1 = terms1.append(k1);
	}
	else {
	  terms1 = terms1.append(k1, k2);
	}
      }
    }
    // second, try alpha^-1 expansion
    boolean done;
    do {
      done = true;
      for (int i = 0; i < alphas.size(); i++) {
	TBTriple alpha = (TBTriple)alphas.elementAt(i);
	if (terms1.member(alpha.getB()) &&
	    terms1.member(alpha.getC()) &&
	    !terms1.member(alpha.getA())) {
	  terms1.addElement(alpha.getA());
	  done = false;
	}
      }
    } while (!done);
    // finally, recurse only when locally consistent
    if ((terms1.size() > terms.size()) &&
	(!terms1.isLocallyConsistent())) {
      return new TBParVec(0);
    }
    return particleClosureBeta(terms1, alphas, betas);
  }

  static TBParVec particleClosureBeta(TBPar terms, Vect alphas, Vect betas) {
    // try a beta expansion
    for (int i = 0; i < terms.size(); i++) {
      LiveExprNode ln = terms.exprAt(i);
      LiveExprNode k1 = null, k2 = null;
      if (ln instanceof LNEven) {
	k1 = ((LNEven)ln).getBody();
	k2 = new LNNext(ln);
      }
      else if (ln instanceof LNDisj) {
	k1 = ((LNDisj)ln).getBody(0);
	k2 = ((LNDisj)ln).getBody(1);
      }
      if ((k1 != null) && !terms.member(k1) && !terms.member(k2)) {
	TBParVec ps1 = particleClosure(terms.append(k1), alphas, betas);
        TBParVec ps2 = particleClosure(terms.append(k2), alphas, betas);
        return ps1.union(ps2);
      }
    }
    // try a beta^-1 expansion
    for (int i = 0; i < betas.size(); i++) {
      TBTriple beta = (TBTriple)betas.elementAt(i); 
      if ((terms.member(beta.getB()) || terms.member(beta.getC())) &&
	  !terms.member(beta.getA())) {
        return particleClosure(terms.append(beta.getA()), alphas, betas);
      }
    }
    // if there are not any more expansions to do, return the terms
    // we've got as the only particle in a list of particles.
    TBParVec res = new TBParVec(1);
    res.addElement(terms);
    return res;
  }

  /**
   * Parse the temporals and impliedTemporals given in the config file.
   * It returns null if there is nothing to check.
   */
  public static LiveExprNode parseLiveness(Tool tool) {
    Action[] fairs = tool.getTemporals();
    LNConj lnc = new LNConj(fairs.length);
    for (int i = 0; i < fairs.length; i++) {
      LiveExprNode ln = astToLive(tool, (ExprNode)fairs[i].pred, fairs[i].con);
      lnc.addConj(ln);
    }
    Action[] checks = tool.getImpliedTemporals();
    if (checks.length == 0) {
      if (fairs.length == 0) {
	return null;
      }
    }
    else if (checks.length == 1) {
      LiveExprNode ln = astToLive(tool, (ExprNode)checks[0].pred, checks[0].con);
      if (lnc.getCount() == 0) {
	return new LNNeg(ln);
      }
      lnc.addConj(new LNNeg(ln));
    }
    else {
      LNDisj lnd = new LNDisj(checks.length);
      for (int i = 0; i < checks.length; i++) {
	LiveExprNode ln = astToLive(tool, (ExprNode)checks[i].pred, checks[i].con);
	lnd.addDisj(new LNNeg(ln));
      }
      if (lnc.getCount() == 0) return lnd;
      lnc.addConj(lnd);
    }
    return lnc;
  }
      
  /**
   * The method processLiveness normalizes the list of temporals and
   * impliedTemporals to check their validity, and to figure out the
   * order and manner in which things should ultimately be checked.
   * This method returns a handle, which can subsequently be passed to
   * the other liveness things.
   *
   * Theory: we're looking for counterexamples to:
   *        spec /\ livespec => []inv /\ livecheck
   * i.e. (spec /\ livespec /\ <>-inv) \/ (spec /\ livespec /\ -livecheck)
   * The first half of this disjunction (inv) is already checked by the
   * model checker on the fly.  We're converting the second half into
   * normal form. We actually omit spec in what we produce. It will be
   * left implicit.  So, the only job is to turn livespec /\ -livecheck:
   *     live1 /\ live2 ... /\ (-check1 \/ -check2 ...)
   * into normal form.
   */
  public static OrderOfSolution[] processLiveness(Tool tool, String metadir) {
    LiveExprNode lexpr = parseLiveness(tool);

    if (lexpr == null) {
      return new OrderOfSolution[0];
    }
    
    // Give tags to all action and state predicates, for equality
    // checking.  We tag them here so that, if DNF should happen to
    // duplicate exprs, then they will still have the same tag.
    lexpr.tagExpr(1);
    lexpr = lexpr.simplify().toDNF();
    if ((lexpr instanceof LNBool) && !((LNBool)lexpr).b) {
      return new OrderOfSolution[0];  // must be unsatisfiable
    }
    LNDisj dnf = (lexpr instanceof LNDisj) ? (LNDisj)lexpr : (new LNDisj(lexpr));

    // Now we will turn DNF into a format that can be tested by the 
    // tableau method. The first step is to collect everything into
    // pems+lexps: listof-(listof-<>[],[]<> /\ tf)
    OSExprPem[] pems = new OSExprPem[dnf.getCount()];
    LiveExprNode[] tfs = new LiveExprNode[dnf.getCount()];
    for (int i = 0; i < dnf.getCount(); i++) {
      // Flatten junctions, because DNF may contain singleton junctions
      LiveExprNode ln = dnf.getBody(i).flattenSingleJunctions();
      OSExprPem pem = new OSExprPem();
      pems[i] = pem;
      if (ln instanceof LNConj) {
        LNConj lnc2 = (LNConj)ln;
        for (int j = 0; j < lnc2.getCount(); j++) {
	  classifyExpr(lnc2.getBody(j), pem);
	}
      } 
      else {
	classifyExpr(ln, pem);
      }
      tfs[i] = null;      
      if (pem.tfs.size() == 1) {
	tfs[i] = (LiveExprNode)pem.tfs.elementAt(0);
      }
      else if (pem.tfs.size() > 1) {
	LNConj lnc2 = new LNConj(pem.tfs.size()); 
	for (int j = 0; j < pem.tfs.size(); j++) {
	  lnc2.addConj((LiveExprNode)pem.tfs.elementAt(j));
	}
	tfs[i] = lnc2;	
      }
    }

    // Now, we will create our OrderOfSolutions. We lump together all
    // disjunctions that have the same tf. This will happen often in
    // cases such as (WF /\ SF) => (WF /\ SF /\ TF), since the WF and
    // SF will be broken up into many cases and the TF will remain the
    // same throughout. (Incidentally, we're checking equality on TFs
    // just syntactically. This is hopefully sufficient, because we
    // haven't done any real rearrangement of them, apart from munging
    // up \/ and /\ above them.  tfbin contains the different tf's.
    // pembin is a vect of vect-of-pems collecting each tf's pems.
    TBPar tfbin = new TBPar(dnf.getCount());
    Vect pembin = new Vect(dnf.getCount());
    for (int i = 0; i < dnf.getCount(); i++) {
      int found = -1;
      LiveExprNode tf = tfs[i];
      for (int j = 0; j < tfbin.size() && found == -1; j++) {
        LiveExprNode tf0 = tfbin.exprAt(j);
        if ((tf == null && tf0 == null) ||
	    (tf != null && tf0 != null && tf.equals(tf0))) {
	  found = j;
	}
      }
      if (found == -1) {
	found = tfbin.size();
        tfbin.addElement(tf);
        pembin.addElement(new Vect());
      }
      ((Vect)pembin.elementAt(found)).addElement(pems[i]);
    }

    // We then create an OrderOfSolution for each tf in tfbin.
    OrderOfSolution[] oss = new OrderOfSolution[tfbin.size()];
    for (int i = 0; i < tfbin.size(); i++) {
      oss[i] = new OrderOfSolution();
      LiveExprNode tf = tfbin.exprAt(i);

      if (tf == null) {
        oss[i].tableau = null;
        oss[i].promises = new LNEven[0];
      }
      else {
        LiveExprNode tf1 = tf.makeBinary();
	oss[i].tableau = constructTableau(tf1, 0);
        TBPar promises = new TBPar(10);
        tf1.extractPromises(promises);
        oss[i].promises = new LNEven[promises.size()]; 
	for (int j = 0; j < promises.size(); j++) {
	  oss[i].promises[j] = (LNEven)promises.exprAt(j);
	}
      }

      // We lump all the pems into a single checkState and checkAct,
      // and oss[i].pems will simply be integer lookups into them.
      Vect stateBin = new Vect();
      Vect actionBin = new Vect();
      Vect tfPems = (Vect)pembin.elementAt(i);
      oss[i].pems = new PossibleErrorModel[tfPems.size()];
      for (int j = 0; j < tfPems.size(); j++) {
        OSExprPem pem = (OSExprPem)tfPems.elementAt(j);
        oss[i].pems[j] = new PossibleErrorModel();
        oss[i].pems[j].AEAction = addToBin(pem.AEAction, actionBin);
        oss[i].pems[j].AEState = addToBin(pem.AEState, stateBin);
        oss[i].pems[j].EAAction = addToBin(pem.EAAction, actionBin);
      }
      // Finally, store the bins with the order of solution.
      oss[i].checkState = new LiveExprNode[stateBin.size()];
      for (int j = 0; j < stateBin.size(); j++) {
	oss[i].checkState[j] = (LiveExprNode)stateBin.elementAt(j);	
      }
      oss[i].checkAction = new LiveExprNode[actionBin.size()];    
      for (int j = 0; j < actionBin.size(); j++) {
	oss[i].checkAction[j] = (LiveExprNode)actionBin.elementAt(j);
      }
    }
    MP.printMessage(EC.TLC_LIVE_IMPLIED, String.valueOf(oss.length));
    // SZ Jul 28, 2009: What for?
    // ToolIO.out.flush();

    return oss;
  }

  /**
   * Given a list of checks, ensures that the checks are in the bin.
   * It returns an array of index of the checks in the bin.
   */
  static int addToBin(LiveExprNode check, Vect bin) {
    if (check == null) return -1;
    int len = bin.size();
    int idx;
    for (idx = 0; idx < len; idx++) {
      LiveExprNode ln = (LiveExprNode)bin.elementAt(idx);
      if (check.equals(ln)) { break; }
    }
    if (idx >= len) {
      bin.addElement(check);
    }
    return idx;
  }
    
  static int[] addToBin(Vect checks, Vect bin) {
    int[] index = new int[checks.size()];
    for (int i = 0; i < checks.size(); i++) {
      LiveExprNode check = (LiveExprNode)checks.elementAt(i);
      index[i] = addToBin(check, bin);
    }
    return index;
  }

  /**
   * A conjunct makes up of exprs of forms <>[]act, []<>act,
   * []<>state, and tf.  For a model to be a valid counterexample, it
   * must pass all of these tests.  This method classifies an
   * expression into <>[]act, []<>act, []<>state, temporal formulas
   * (without actions), or erroneous things.
   */
  static void classifyExpr(LiveExprNode ln, OSExprPem pem) {
    if (ln instanceof LNEven) {
      LiveExprNode ln1 = ((LNEven)ln).getBody();
      if (ln1 instanceof LNAll) {
	LiveExprNode ln2 = ((LNAll)ln1).getBody();
	if (ln2.getLevel() < 3) {
	  pem.EAAction.addElement(ln2);
	  return;
	}
      }
    }
    else if (ln instanceof LNAll) {
      LiveExprNode ln1 = ((LNAll)ln).getBody();
      if (ln1 instanceof LNEven) {
	LiveExprNode ln2 = ((LNEven)ln1).getBody();
	int level = ln2.getLevel();
	if (level <= 1) {
	  pem.AEState.addElement(ln2);
	  return;
	}
        if (level == 2) {
	  pem.AEAction.addElement(ln2);
	  return;
	}
      }
    }
    if (ln.containAction()) 
    {
        Assert.fail(EC.TLC_LIVE_WRONG_FORMULA_FORMAT);
    }
    pem.tfs.addElement(ln);
  }

// SZ Jul 28, 2009: not used
//  /**
//   * @deprecated not used
//   */
//  public static void printTBGraph(TBGraph tableau) {
//      if (tableau == null) 
//      {
//          ToolIO.out.println("No tableau.");
//      } else {
//          ToolIO.out.println(tableau.toString());
//      }
//  }

  /**
   * OSExprPem is a temporary data structure for producing the
   * PossibleErrorModel and OrderOfSolution.
   */
  private static class OSExprPem {
    Vect EAAction;     // <>[]action's
    Vect AEState;      // []<>state's
    Vect AEAction;     // []<>action's
    Vect tfs;          // other temp formulae with no actions

    public OSExprPem() {
      this.EAAction = new Vect();
      this.AEState = new Vect();
      this.AEAction = new Vect();
      this.tfs = new Vect();
    }
  }

}
