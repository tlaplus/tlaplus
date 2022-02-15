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
import tla2sany.semantic.LevelConstants;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.Action;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.EvalControl;
import tlc2.tool.IContextEnumerator;
import tlc2.tool.ITool;
import tlc2.tool.ModelChecker;
import tlc2.tool.Specs;
import tlc2.tool.TLCState;
import tlc2.tool.ToolGlobals;
import tlc2.util.Context;
import tlc2.util.Vect;
import tlc2.value.IBoolValue;
import tlc2.value.IFcnLambdaValue;
import tlc2.value.IValue;
import tlc2.value.impl.EvaluatingValue;
import tlc2.value.impl.MethodValue;
import util.Assert;
import util.ToolIO;

public class Liveness implements ToolGlobals, ASTConstants {

	private static LiveExprNode astToLive(ITool tool, ExprNode expr, Context con, int level) {
		/*
		 * MAK 04/16/2021: Arguments of a non-zero arity operator that do not appear on
		 * the operator's right-hand side (commonly called ignored arguments), are
		 * ignored by level-checking, regardless of what the arguments are replaced with
		 * in places where the operator is evaluated. For example, the operator `Op`
		 * below has constant-level because its `a` argument does not appear in `Op`'s
		 * definition, even though it is evaluated in `Prop` with the state-level
		 * variable `v`.
		 * 
		 * ----- MODULE Frob ------
		 * 
		 * EXTENDS Naturals
		 * 
		 * VARIABLE v
		 * 
		 * Op(a,b) == b = 42
		 * 
		 * Spec == v = 0 /\ [][UNCHANGED v]_v
		 * 
		 * Prop == <>Op(v, 42)
		 * 
		 * ======
		 * 
		 * This causes the following error, iff the operator appears in a (temporal)
		 * property and has a Java module override (even if the module override ignores
		 * the argument(s) as well):
		 * 
		 * "In evaluation, the identifier v is either undefined or not an operator."
		 * 
		 * The reason is that Tool.java passes all arguments to the Java module
		 * overrides; even ignored ones (the signature of the Java module override has
		 * to match the signature of the TLA+ operator for the override to be loaded).
		 * 
		 * Below is a excerpt of operators, from the (extended) list of standard
		 * operators, that are affected when evaluated with > *constant-level* arguments
		 * in a (liveness) property:
		 * 
		 * `TLC!Print` (when `out` argument has state-level), `TLC!PrintT`,
		 * `TLC!Assert`, `TLC!TLCGet`, `TLC!TLCSet`
		 * 
		 * Some more examples of modules that lack proper definitions from the
		 * CommunityModules:
		 * 
		 * CSV.tla, IOUtils.tla, SVG.tla (`SVGElemToString`, `NodeOfRingNetwork`), ...
		 * 
		 * Obviously, we could mandate all operators to be properly defined. However,
		 * the definitions in TLC.tla would have to become e.g.:
		 * 
		 * `PrintT(out) == out = out` or `TLCGet(i) == CHOOSE n : i = i`
		 * 
		 * The standard modules are defined in the book "Specifying Systems", which is
		 * one reason not to change them. Another is that the definitions look funny.
		 * 
		 * We could also choose to declare this a corner case and move on. After all,
		 * the bug is limited to operators with Java module overrides, which may not
		 * commonly occur in liveness properties. However, the community has started to
		 * embrace module overrides to speed up model-checking, and it is not uncommon
		 * for operators with Java module overrides to be defined as TRUE.
		 * 
		 * Thus, the if block below takes the level of the arguments in the operator
		 * application into account. The overhead of this change is negligible and only
		 * incurred at startup (during the construction of the liveness tableau).
		 * Additionally, it only checks the level for MethodValues and EvaluatingValues.
		 */
		if (level == LevelConstants.ConstantLevel && expr instanceof OpApplNode) {
			final Object realDef = tool.lookup(((OpApplNode) expr).getOperator(), Context.Empty, false);
			if (realDef instanceof MethodValue || realDef instanceof EvaluatingValue) {
				// The current level is determined by the maximum level of the arguments in the
				// operator's application.
				for (SymbolNode p : expr.getAllParams()) {
					level = Math.max(level, p.getLevel());
				}
			}
		}

		if (level == LevelConstants.ConstantLevel) {
			final IValue val = tool.eval(expr, con, TLCState.Empty);
			if (!(val instanceof IBoolValue)) {
				Assert.fail(EC.TLC_EXPECTED_VALUE, new String[] { "boolean", expr.toString() });
			}
			return ((IBoolValue) val).getVal() ? LNBool.TRUE : LNBool.FALSE;
		} else if (level == LevelConstants.VariableLevel) {
			return new LNStateAST(expr, con);
		} else {
			// Assert.check(level == LevelConstants.ActionLevel;
			return new LNAction(expr, con);
		}
	}

	/**
	 * The method astToLive converts an ExprNode into a LiveExprNode. o We are
	 * passing down a tool and a context as we parse the expressions
	 * recursively. That's for calling eval(). o The method has some
	 * restrictions. If you did Predicate([]p), then we'd need to instantiate
	 * the predicate body with []p. For the moment, we require that arguments to
	 * predicates be computable from its context.
	 */
	private static LiveExprNode astToLive(ITool tool, ExprNode expr, Context con) {
		switch (expr.getKind()) {
		case OpApplKind: {
			OpApplNode expr1 = (OpApplNode) expr;
			return astToLiveAppl(tool, expr1, con);
		}
		case LetInKind: {
			LetInNode expr1 = (LetInNode) expr;
			return astToLive(tool, expr1.getBody(), con);
		}
		case SubstInKind: {
			SubstInNode expr1 = (SubstInNode) expr;
			Subst[] subs = expr1.getSubsts();
			int slen = subs.length;
			Context con1 = con;
			for (int i = 0; i < slen; i++) {
				Subst sub = subs[i];
				con1 = con1.cons(sub.getOp(), tool.getVal(sub.getExpr(), con, false));
			}
			return astToLive(tool, expr1.getBody(), con1);
		}
		default: {
			int level = Specs.getLevel(expr, con);
			if (level > LevelConstants.ActionLevel) {
				Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, expr.toString());
			}
			return astToLive(tool, expr, con, level);
		}
		}
	}

	private static LiveExprNode astToLiveAppl(ITool tool, OpApplNode expr, Context con) {
		ExprOrOpArgNode[] args = expr.getArgs();
		int alen = args.length;
		SymbolNode opNode = expr.getOperator();
		int opcode = BuiltInOPs.getOpCode(opNode.getName());

		if (opcode == 0) {
			// This is a user-defined operator with one exception: it may
			// be substed by a builtin operator. This special case is handled
			// by checking if the lookup returns a OpDef with opcode = 0.
			Object val = tool.lookup(opNode, con, false);

			if (val instanceof OpDefNode) {
				OpDefNode opDef = (OpDefNode) val;
				opcode = BuiltInOPs.getOpCode(opDef.getName());
				if (opcode == 0) {
					try {
						FormalParamNode[] formals = opDef.getParams();
						Context con1 = con;
						for (int i = 0; i < alen; i++) {
							IValue argVal = tool.eval(args[i], con, TLCState.Empty);
							con1 = con1.cons(formals[i], argVal);
						}
						LiveExprNode res = astToLive(tool, opDef.getBody(), con1);
						int level = res.getLevel();
						if (level > LevelConstants.ActionLevel) {
							return res;
						}
						return astToLive(tool, expr, con, level);
					} catch (Exception e) { /* SKIP */
					}
				}
			} else if (val instanceof IBoolValue) {
				return ((IBoolValue) val).getVal() ? LNBool.TRUE : LNBool.FALSE;
			}

			if (opcode == 0) {
				int level = Specs.getLevel(expr, con);
				if (level > LevelConstants.ActionLevel) {
					Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, expr.toString());
				}
				return astToLive(tool, expr, con, level);
			}
		}

		switch (opcode) {
		case OPCODE_be: // BoundedExists
		{
			ExprNode body = (ExprNode) args[0];
			try {
				IContextEnumerator Enum = tool.contexts(expr, con, TLCState.Empty, TLCState.Empty, EvalControl.Clear);
				Context con1;
				LNDisj res = new LNDisj(0);
				while ((con1 = Enum.nextElement()) != null) {
					LiveExprNode kid = astToLive(tool, body, con1);
					res.addDisj(kid);
				}
				int level = res.getLevel();
				if (level > LevelConstants.ActionLevel) {
					return res;
				}
				return astToLive(tool, expr, con, level);
			} catch (Exception e) {
				// Catching Exception here seem dangerous
				// Assert.printStack(e);
				int level = Specs.getLevel(expr, con);
				if (level > LevelConstants.ActionLevel) {
					Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, expr.toString());
					;
				}
				return astToLive(tool, expr, con, level);
			}
		}
		case OPCODE_bf: // BoundedForall
		{
			ExprNode body = (ExprNode) args[0];
			try {
				IContextEnumerator Enum = tool.contexts(expr, con, TLCState.Empty, TLCState.Empty, EvalControl.Clear);
				Context con1;
				LNConj res = new LNConj(0);
				while ((con1 = Enum.nextElement()) != null) {
					LiveExprNode kid = astToLive(tool, body, con1);
					res.addConj(kid);
				}
				int level = res.getLevel();
				if (level > LevelConstants.ActionLevel) {
					return res;
				}
				return astToLive(tool, expr, con, level);
			} catch (Exception e) {
				// Catching Exception here seem dangerous
				// Assert.printStack(e);
				int level = Specs.getLevel(expr, con);
				if (level > LevelConstants.ActionLevel) {
					if (e instanceof Assert.TLCRuntimeException) {
						Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, new String[] {expr.toString(), e.getMessage()});
					} else {
						Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, expr.toString());
					}
				}
				return astToLive(tool, expr, con, level);
			}
		}
		case OPCODE_cl: // ConjList
		case OPCODE_land: {
			LNConj lnConj = new LNConj(alen);
			for (int i = 0; i < alen; i++) {
				LiveExprNode kid = astToLive(tool, (ExprNode) args[i], con);
				lnConj.addConj(kid);
			}
			int level = lnConj.getLevel();
			if (level > LevelConstants.ActionLevel) {
				return lnConj;
			}
			return astToLive(tool, expr, con, level);
		}
		case OPCODE_dl: // DisjList
		case OPCODE_lor: {
			LNDisj lnDisj = new LNDisj(alen);
			for (int i = 0; i < alen; i++) {
				LiveExprNode kid = astToLive(tool, (ExprNode) args[i], con);
				lnDisj.addDisj(kid);
			}
			int level = lnDisj.getLevel();
			if (level > LevelConstants.ActionLevel) {
				return lnDisj;
			}
			return astToLive(tool, expr, con, level);
		}
		case OPCODE_fa: // FcnApply
		{
			try {
				IValue fval = tool.eval(args[0], con, TLCState.Empty);
				if (fval instanceof IFcnLambdaValue) {
					IFcnLambdaValue fcn = (IFcnLambdaValue) fval;
					if (!fcn.hasRcd()) {
						// this could be a bug, since con1 is created but not
						// used
						// SZ Jul 13, 2009: removed to kill the warning
						// SZ Feb 20, 2009: variable never read locally
						// Context con1 =
						tool.getFcnContext(fcn, args, con, TLCState.Empty, TLCState.Empty, EvalControl.Clear);
						return astToLive(tool, (ExprNode) fcn.getBody(), con);
					}
				}
			} catch (Exception e) { /* SKIP */
				// Swallowing Exception here seem dangerous
			}
			int level = expr.getLevel();
			if (level > LevelConstants.ActionLevel) {
				Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, expr.toString());
			}
			return astToLive(tool, expr, con, level);
		}
		case OPCODE_ite: // IfThenElse
		{
			LiveExprNode guard = astToLive(tool, (ExprNode) args[0], con);
			LiveExprNode e1 = astToLive(tool, (ExprNode) args[1], con);
			LiveExprNode e2 = astToLive(tool, (ExprNode) args[2], con);
			LiveExprNode conj1 = new LNConj(guard, e1);
			LiveExprNode conj2 = new LNConj(new LNNeg(guard), e2);
			LiveExprNode res = new LNDisj(conj1, conj2);
			int level = res.getLevel();
			if (level > LevelConstants.ActionLevel) {
				return res;
			}
			return astToLive(tool, expr, con, level);
		}
		case OPCODE_lnot: {
			LiveExprNode lnArg = astToLive(tool, (ExprNode) args[0], con);
			int level = lnArg.getLevel();
			if (level > LevelConstants.ActionLevel) {
				return new LNNeg(lnArg);
			}
			return astToLive(tool, expr, con, level);
		}
		case OPCODE_implies: {
			LiveExprNode lnLeft = astToLive(tool, (ExprNode) args[0], con);
			LiveExprNode lnRight = astToLive(tool, (ExprNode) args[1], con);
			int level = Math.max(lnLeft.getLevel(), lnRight.getLevel());
			if (level > LevelConstants.ActionLevel) {
				return new LNDisj(new LNNeg(lnLeft), lnRight);
			}
			return astToLive(tool, expr, con, level);
		}
		case OPCODE_prime: {
			return new LNAction(expr, con);
		}
		case OPCODE_sf: // SF
		{
			// expand SF_e(A) into <>[]-EN<A>_e \/ []<><A>_e
			ExprNode subs = (ExprNode) args[0]; // the e in SF_e(A)
			ExprNode body = (ExprNode) args[1]; // the A in SF_e(A)
			LiveExprNode en = new LNNeg(new LNStateEnabled(body, con, subs, false));
			LiveExprNode act = new LNAction(body, con, subs, false);
			return new LNDisj(new LNEven(new LNAll(en)), new LNAll(new LNEven(act)));
		}
		case OPCODE_wf: // WF
		{
			// expand WF_e(A) into []<>(-EN<A>_e \/ <A>_e)
			ExprNode subs = (ExprNode) args[0]; // the e in WF_e(A)
			ExprNode body = (ExprNode) args[1]; // the A in WF_e(A)
			LiveExprNode ln1 = new LNNeg(new LNStateEnabled(body, con, subs, false));
			LiveExprNode ln2 = new LNAction(body, con, subs, false);
			LiveExprNode disj = new LNDisj(ln1, ln2);
			return new LNAll(new LNEven(disj));
		}
		case OPCODE_leadto: {
			// F ~> G equals [](F => <>G), however TLC does not have an
			// implementation for logical implication. Thus, the rule of
			// material implication ("->") is used to transform it into a
			// disjunct.
			LiveExprNode lnLeft = astToLive(tool, (ExprNode) args[0], con);
			LiveExprNode lnRight = astToLive(tool, (ExprNode) args[1], con);
			// expand a ~> b into [](-a \/ <>b) 
			LNDisj lnd = new LNDisj(new LNNeg(lnLeft), new LNEven(lnRight));
			return new LNAll(lnd);
		}
		case OPCODE_box: {
			LiveExprNode lnArg = astToLive(tool, (ExprNode) args[0], con);
			return new LNAll(lnArg);
		}
		case OPCODE_diamond: {
			LiveExprNode lnArg = astToLive(tool, (ExprNode) args[0], con);
			return new LNEven(lnArg);
		}
		case OPCODE_aa: { // AngleAct <A>_e
			assert Specs.getLevel(expr, con) == LevelConstants.ActionLevel;
			final ExprNode body = (ExprNode) args[0]; // the A in <<A>>_e
			final ExprNode subs = (ExprNode) args[1]; // the e in <<A>>_e
			return new LNAction(body, con, subs, false);
		}

		// The following case added by LL on 13 Nov 2009 to handle subexpression
		// names.
		case OPCODE_nop: {
			return astToLive(tool, (ExprNode) args[0], con);
		}
		default: {
			// We handle all the other built-in operators here. Surprisingly, even OPCODE_aa
			// (AngleAct <A>_e) is handled here and not as the dedicated case statement below
			// such that e gets passed as subscript to LNAction:
			//
			//		case OPCODE_aa: { // AngleAct <A>_e
			//			assert Spec.getLevel(expr, con) == 2;
			//			final ExprNode body = (ExprNode) args[0]; // the A in <<A>>_e
			//			final ExprNode subscript = (ExprNode) args[1]; // the e in <<A>>_e
			//			return new LNAction(body, con, subscript, false);
			//		}
			//
			// The default handling here results in LNAction#subscript to be null skipping
			// the subscript related branch in LNAction#eval(Tool, TLCState, TLCState). This
			// poses no problem though because Tool#evalAppl eventually checks if e' = e.
			int level = Specs.getLevel(expr, con);
			if (level > LevelConstants.ActionLevel) {
				Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, expr.toString());
			}
			return astToLive(tool, expr, con, level);
		}
		}
	}

	/**
	 * Parse the temporals and impliedTemporals given in the config file. It
	 * returns null if there is nothing to check.
	 */
	private static LiveExprNode parseLiveness(ITool tool) {
		// livespec (fairness)
		// For example, a conjunct with context for each WF in `\A self \in ProcSet :
		// WF_vars(Next(self))`.
		Action[] fairs = tool.getTemporals();
		LNConj lnc = new LNConj(fairs.length);
		for (int i = 0; i < fairs.length; i++) {
			LiveExprNode ln = astToLive(tool, (ExprNode) fairs[i].pred, fairs[i].con);
			lnc.addConj(ln);
		}
		
		// livecheck
		Action[] checks = tool.getImpliedTemporals();
		if (checks.length == 0) {
			if (fairs.length == 0) {
				// No PROPERTIES and no fairness.
				return null;
			}
		} else if (checks.length == 1) {
			// Avoid outer disjunct if just one branch (singleton junctions).
			LiveExprNode ln = astToLive(tool, (ExprNode) checks[0].pred, checks[0].con);
			if (lnc.getCount() == 0) {
				// We are looking for ~livecheck. Thus, nest ln in LNNeg (same below).
				return new LNNeg(ln);
			}
			// /\ livespec 
			// /\ ~livecheck
			lnc.addConj(new LNNeg(ln));
		} else {
			LNDisj lnd = new LNDisj(checks.length);
			for (int i = 0; i < checks.length; i++) {
				LiveExprNode ln = astToLive(tool, (ExprNode) checks[i].pred, checks[i].con);
				lnd.addDisj(new LNNeg(ln));
			}
			if (lnc.getCount() == 0) {
				return lnd;
			}
			// /\ livespec 
			// /\ \/ ~livecheck1
			//    \/ ~livecheck2
			//    \/ ...
			lnc.addConj(lnd);
		}
		return lnc;
	}

	/**
	 * The method processLiveness normalizes the list of temporals and
	 * impliedTemporals to check their validity, and to figure out the order and
	 * manner in which things should ultimately be checked. This method returns
	 * a handle, which can subsequently be passed to the other liveness things.
	 *
	 * Theory: we're looking for counterexamples to:
	 * 
	 * <pre>
	 * spec /\ livespec => []inv /\ livecheck
	 * </pre>
	 * 
	 * i.e.
	 * 
	 * <pre>
	 * \/ (spec /\ livespec /\ <>-inv)
	 * \/ (spec /\ livespec /\ -livecheck)
	 * </pre>
	 * 
	 * <p>
	 * The first half of this disjunction (inv) is already checked by the model
	 * checker on the fly (@see
	 * {@link ModelChecker#doNext(TLCState, tlc2.util.ObjLongTable)}).
	 * <p>
	 * We're converting the second half into <i>normal form</i>. We actually
	 * omit spec in what we produce. It will be left implicit. So, the only job
	 * is to turn:
	 * 
	 * <pre>
	 * livespec /\ -livecheck
	 * </pre>
	 * 
	 * into:
	 * 
	 * <pre>
	 * live1 /\ live2 ... /\ (-check1 \/ -check2 ...)
	 * </pre>
	 * 
	 * into <i>normal form</i>. livespec corresponds to the spec's
	 * <i>fairness</i> formulae where check1, check2, ... are the actual
	 * <i>liveness properties</i> to be checked.
	 */
	public static OrderOfSolution[] processLiveness(final ITool tool) {
		LiveExprNode lexpr = parseLiveness(tool);

		// Contrary to the Manna & Pnueli book - which discusses LTL and LTL with only
		// future operators - the Temporal Logic of Actions (TLA) comes with actions. If
		// there is a reduction from TLA to LTL (with only future operators), it is not
		// used here.  Instead, the code below has special treatment for actions (LNAction),
		// which is not part of the Manna & Pnueli book.
		
		if (lexpr == null) {
			return new OrderOfSolution[0];
		}

		// I:
		// Give tags to all action and state predicates, for equality
		// checking (tlc2.tool.liveness.LiveExprNode.equals(LiveExprNode)).
		// We tag them here so that, if disjunct normal form (DNF) should happen to
		// duplicate expressions, then they will still have the same tag.
		lexpr.tagExpr(1);
		
		// II & III:
		// Converting the formula to DNF pushes negation inside (see
		// LiveExprNode#pushNeg). This is important later when the promises are
		// extracted (see LiveExprNode#extractPromises).
		lexpr = lexpr.simplify().toDNF();
		if ((lexpr instanceof LNBool) && !((LNBool) lexpr).b) {
			// This branch is only reachable for a handful of properties, such as
			// `<>[]TRUE => TRUE` -- simplify/toDNF move the LNBool to the top.
			// However, simplify/toDNF does not work for other properties to be
			// identified as tautologies (`<>TRUE`, `<>[]TRUE`, ...).  
			return new OrderOfSolution[0]; // must be unsatisfiable
		}
		final LNDisj dnf = (lexpr instanceof LNDisj) ? (LNDisj) lexpr : (new LNDisj(lexpr));

		// IV:
		// Now we will turn DNF into a format that can be tested by the
		// tableau method. The first step is to collect everything into
		// pems+lexps: listof-(listof-<>[],[]<> /\ tf).
		//
		// "pems":  Possible Error Models
		// "lexps": Liveness expressions ?
		//
		// In other words, for each junction of the disjunct normal form, classify DNF
		// into four Vects in OSExprPem with A an action and S a state-predicate:
		//
		// 1) <>[]A: "Eventually Always Actions"        OSExprPem#AEAction
		// 2) []<>A: "Always Eventually Actions"        OSExprPem#EAAction
		// 3) <>[]S: "Eventually Always States"         OSExprPem#AEState
		// 4) tf:   "temporal formulae with no actions" OSExprPem#tfs
		//
		// For example, below is what happens for a simple spec:
		//
		//  VARIABLE x
		//  Spec == x = 0 /\ [][x'=x+1]_x /\ WF_x(x'=x+1)     \* LNDisj(LNNeg(LNStateEnabled) \/ LNAction) in OSExprPem#AEAction
		//
		//  Prop1 == <>[][x' > x]_x                           \* LNNeg(LNAction) in OSExprPem#AEAction
		//  Prop2 == []<>(<<x' > x>>_x)                       \* LNNeg(LNAction) in OSExprPem#EAAction
		//  Prop3 == <>[](x \in Nat)                          \* LNNeg(LNState)  in OSExprPem#AEState
		//  Prop4 == <>(x \in Nat)                            \* LNAll(LNNeg(LNStateAST) in OSExprPem#tfs
		//
		final OSExprPem[] pems = new OSExprPem[dnf.getCount()];
		final LiveExprNode[] tfs = new LiveExprNode[dnf.getCount()];
		for (int i = 0; i < dnf.getCount(); i++) {
			// Flatten junctions, because DNF may contain singleton junctions
			// (a singleton junction is a disjunct list of a single disjunct).
			// Flattening is, thus, a simple optimization that rewrites the body
			// to remove superfluous disjunct operators. 
			final LiveExprNode ln = dnf.getBody(i).flattenSingleJunctions();
			final OSExprPem pem = new OSExprPem();
			pems[i] = pem;
			if (ln instanceof LNConj) {
				final LNConj lnc2 = (LNConj) ln;
				for (int j = 0; j < lnc2.getCount(); j++) {
					classifyExpr(lnc2.getBody(j), pem);
				}
			} else {
				classifyExpr(ln, pem);
			}
			tfs[i] = pem.toTFS();
		}
		// Could null pems[n].tfs at this point.

		// V:
		// Now, we will create our OrderOfSolutions. We lump together all
		// disjunctions that have the same tf. This will happen often in
		// cases such as (WF /\ SF) => (WF /\ SF /\ TF), since the WF and
		// SF will be broken up into many cases and the TF will remain the
		// same throughout. (Incidentally, we're checking equality on TFs
		// just syntactically. This is hopefully sufficient, because we
		// haven't done any real rearrangement of them, apart from munging
		// up \/ and /\ above them. tfbin contains the different tf's.
		// pembin is a vect of vect-of-pems collecting each tf's pems.
		final TBPar tfbin = new TBPar(dnf.getCount());
		final Vect<Vect<OSExprPem>> pembin = new Vect<>(dnf.getCount());
		for (int i = 0; i < dnf.getCount(); i++) {
			int found = -1;
			final LiveExprNode tf = tfs[i];
			// Compare current temporal formula to all other temporal formulae added to
			// tfbin so far.
			for (int j = 0; j < tfbin.size() && found == -1; j++) {
				final LiveExprNode tf0 = tfbin.exprAt(j);
				if ((tf == null && tf0 == null) || (tf != null && tf0 != null && tf.equals(tf0))) {
					// We get here if we fFound two (syntactically) equivalent temporal formulae
					// (null and null are syntactically equivalent). An simple example is:
					//
					//  Spec== x = 0 /\ [][UNCHANGED x]_x /\ SF_x(UNCHANGED x)
					//  Prop== <>TRUE  \* Alternatively, a state-level expression.
					//
					// The tfs that get lumped together are the second conjuncts of:
					//
					//  \/ (/\ (<>[]-ENABLED UNCHANGED x)
				    //      /\ ([]FALSE))
				    //  \/ (/\ ([]<><line UNCHANGED x)
				    //      /\ ([]FALSE))
					// 
					// Out of all the specs on my system, only the following two TLA+ examples trigger
					// this code path (with `tf#null`), though:
					//   specifications/SpecifyingSystems/TLC/MCAlternatingBit.tla
					//   specifications/allocator/SimpleAllocator.tla
					// They have in common that their livecheck and livespec (fairness) are of the form:
					//
					//  Fairness== \A self \in SetOfProcs: SF_vars(...)
					//  Prop== \A self \in SetOfProcs: P ~> Q
					//
					// In those specs, this optimizations substantially reduces the blowup caused by
					// the universal quantifier.
					//
					//TODO: Investigate how substantial reduction, if a more sophisticated (beyond syntax)
					//      equivalence was implemented (the liveness graph is the cross-product of the
					//      state-graph and tableau!).
					found = j;
				}
			}
			if (found == -1) {
				found = tfbin.size();
				tfbin.addElement(tf);
				pembin.addElement(new Vect<OSExprPem>());
			}
			((Vect<OSExprPem>) pembin.elementAt(found)).addElement(pems[i]);
		}
		// Could null pems (OSExprPem) and tfs (LiveExprNode[]) here.

		// VI:
		// We then create an OrderOfSolution for each tf in tfbin.
		final OrderOfSolution[] oss = new OrderOfSolution[tfbin.size()];
		for (int i = 0; i < tfbin.size(); i++) {
			final LiveExprNode tf = tfbin.exprAt(i);

			if (tf == null) {
				oss[i] = new OrderOfSolution(new LNEven[0]);
			} else {
				// Suggested by the comment of tlc2.tool.liveness.LiveExprNode.makeBinary(),
				// validated by running the test suite with this assertion, and manually
				// confirmed by eye-balling
				// tlc2.tool.liveness.Liveness.classifyExpr(LiveExprNode, OSExprPem), tfs[i]
				// is free of LNActions (LNActions are in OSExprPem#EAction and
				// OSExprPem#AEAction.
				//assert !tfs[i].containAction() : "Found LNAction(s) in temporal formulae.";
				
				// Decompose disjunct and conjunct lists to at most two junctions. E.g.:
				//
				//   /\ tf1
				//   /\ tf2
				//   /\ tf3
				//   /\ tf4
				//
				//  to:
				//
				//   /\ /\ tf1
				//      /\ tf2
				//   /\ /\ tf3
				//      /\ tf4
				//
				// This, usually, has to happen for properties that involve universal
				// quantification:
				//
				//   \A self \in SetOfProcs: P ~> Q
				//
				// Note that LNActions have been excluded from tf in step IV. above as it's
				// mandated in LiveExprNode#makeBinary.  This is because the tableau construction
				// in the Manna & Pnueli book is for LTL that has no actions.  Thus, action
				// are excluded from the tableau, and, instead, get a special treatment in this
				// implementation. 
				final LiveExprNode tf1 = tf.makeBinary();
				// Below is a (non-exhaustive) list of examples for tf (let P and Q be state- or
				// constant-level formulae):
				//
				// Prop: <>P, here: []~P
				// Prop: P ~> Q, here: <>(P /\ []~Q)
				// Prop: [](P => []Q), here: <>(P /\ <>~Q)
				// Prop: [](P => <>[]Q), here: <>(P /\ []<>~Q)
				//
				// Negation has already pushed inside to the atom in toDNF above.
				//assert tf1.isPositiveForm();
				
				// LEN#extractPromises returns all <>(someStateOrConstantLevelFormula), which
				// are added as promises to the OOS.
				TBGraph tbg = new TBGraph(tf1);
				
// Uncomment to write the tableau in dot format to disk.				
//				try {
//					Files.write(Paths.get("./TBGraph.dot"), tbg.toDotViz().getBytes());
//				} catch (IOException e) {
//					// TODO Auto-generated catch block
//					e.printStackTrace();
//				}
				oss[i] = new OrderOfSolution(tbg, tf1.extractPromises());
			}

			// VII:
			// We lump all the pems into a single checkState and checkAct,
			// and oss[i].pems will simply be integer lookups into them.
			//
			// At this point, the temporal formulae are done and only the `[]<>A`, `<>[]A`, and `[]<>S`
			// are added to the OOS.  The OOS holds the `[]<>S` and the union of `[]<>A` and `<>[]A`
			// (OOS#checkState and OOS#checkAction). The PossibleErrorModel stores the indices into
			// OOS#checkState and OOS#checkAction.
			//
			// The split into OrderOfSolution (OOS) and PossibleErrorModel (PEM) appears to
			// be a code-level optimization to speed-up the check of the liveness/behavior-graph
			// in LiveWorker.
			final Vect<LiveExprNode> stateBin = new Vect<>();
			final Vect<LiveExprNode> actionBin = new Vect<>();
			final Vect<OSExprPem> tfPems = (Vect<OSExprPem>) pembin.elementAt(i);
			oss[i].setPems(new PossibleErrorModel[tfPems.size()]);
			for (int j = 0; j < tfPems.size(); j++) {
				final OSExprPem pem = (OSExprPem) tfPems.elementAt(j);
				oss[i].getPems()[j] = new PossibleErrorModel(addToBin(pem.AEAction, actionBin),
						addToBin(pem.AEState, stateBin), addToBin(pem.EAAction, actionBin));
			}
			// Finally, store the bins with the order of solution.
			oss[i].setCheckState(new LiveExprNode[stateBin.size()]);
			for (int j = 0; j < stateBin.size(); j++) {
				oss[i].getCheckState()[j] = (LiveExprNode) stateBin.elementAt(j);
			}
			oss[i].setCheckAction(new LiveExprNode[actionBin.size()]);
			for (int j = 0; j < actionBin.size(); j++) {
				oss[i].getCheckAction()[j] = (LiveExprNode) actionBin.elementAt(j);
			}
		}
		// Could null TBPar tfbin and Vect<Vect<OSExprPem>> pembin here.

		MP.printMessage(EC.TLC_LIVE_IMPLIED, String.valueOf(oss.length));
		// SZ Jul 28, 2009: What for?
		// ToolIO.out.flush();

		return oss;
	}

	/**
	 * Given a list of checks, ensures that the checks are in the bin. It
	 * returns an array of index of the checks in the bin.
	 */
	private static int addToBin(LiveExprNode check, Vect<LiveExprNode> bin) {
		if (check == null) {
			return -1;
		}
		int len = bin.size();
		int idx;
		for (idx = 0; idx < len; idx++) {
			LiveExprNode ln = (LiveExprNode) bin.elementAt(idx);
			if (check.equals(ln)) {
				break;
			}
		}
		if (idx >= len) {
			bin.addElement(check);
		}
		return idx;
	}

	private static int[] addToBin(Vect<LiveExprNode> checks, Vect<LiveExprNode> bin) {
		int[] index = new int[checks.size()];
		for (int i = 0; i < checks.size(); i++) {
			LiveExprNode check = (LiveExprNode) checks.elementAt(i);
			index[i] = addToBin(check, bin);
		}
		return index;
	}

	/**
	 * A conjunct makes up of exprs of forms <>[]act, []<>act, []<>state, and
	 * tf. For a model to be a valid counterexample, it must pass all of these
	 * tests. This method classifies an expression into <>[]act, []<>act,
	 * []<>state, temporal formulas (without actions), or erroneous things.
	 */
	// TODO Explore the idea to syntactically rewrite an LNActions A into a
	// ordinary predicate and the next state operator ()A in the tableau.
	private static void classifyExpr(LiveExprNode ln, OSExprPem pem) {
		// TLC is clever enough to optimize the case where some temporal formula
		// can be handled WITHOUT a tableau. In this case, the state graph IS
		// the behavior graph and thus the overall verification time is reduced.
		// Additionally, the tableau generation does not support formulas 
		// containing (nested) LNActions.
		if (ln instanceof LNEven) {
			LiveExprNode ln1 = ((LNEven) ln).getBody();
			if (ln1 instanceof LNAll) {
				LiveExprNode ln2 = ((LNAll) ln1).getBody();
				if (ln2.getLevel() < LevelConstants.TemporalLevel) {
					pem.EAAction.addElement(ln2);
					return;
				}
			}
		} else if (ln instanceof LNAll) {
			LiveExprNode ln1 = ((LNAll) ln).getBody();
			if (ln1 instanceof LNEven) {
				LiveExprNode ln2 = ((LNEven) ln1).getBody();
				int level = ln2.getLevel();
				if (level <= LevelConstants.VariableLevel) {
					pem.AEState.addElement(ln2);
					return;
				}
				if (level == LevelConstants.ActionLevel) {
					pem.AEAction.addElement(ln2);
					return;
				}
			}
		}
		if (ln.containAction()) {
			Assert.fail(EC.TLC_LIVE_WRONG_FORMULA_FORMAT);
		}
		// If we get here (because of a temporal formula), at tableau is
		// consequently going to be created. This part corresponds to the
		// ideas in the MP book.
		pem.tfs.addElement(ln);
	}

	public static void printTBGraph(TBGraph tableau) {
		if (tableau == null) {
			ToolIO.out.println("No tableau.");
		} else {
			ToolIO.out.println(tableau.toString());
		}
	}

	/**
	 * OSExprPem is a temporary data structure for producing the
	 * PossibleErrorModel and OrderOfSolution.
	 */
	private static class OSExprPem {
		private final Vect<LiveExprNode> EAAction; // <>[]action's
		private final Vect<LiveExprNode> AEState; // []<>state's
		private final Vect<LiveExprNode> AEAction; // []<>action's
		private final Vect<LiveExprNode> tfs; // other temp formulae with no actions

		public OSExprPem() {
			this.EAAction = new Vect<>();
			this.AEState = new Vect<>();
			this.AEAction = new Vect<>();
			this.tfs = new Vect<>();
		}

		public LiveExprNode toTFS() {
			if (tfs.size() == 1) {
				// Once again avoid creating a superfluous LNConj in case of a singleton
				// junction.
				return (LiveExprNode) tfs.elementAt(0);
			} else if (tfs.size() > 1) {
				final LNConj lnc2 = new LNConj(tfs.size());
				for (int j = 0; j < tfs.size(); j++) {
					lnc2.addConj((LiveExprNode) tfs.elementAt(j));
				}
				return lnc2;
			} else {
				return null;
			}
		}
	}

}
