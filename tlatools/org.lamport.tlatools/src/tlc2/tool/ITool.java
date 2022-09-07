/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool;

import java.io.File;
import java.util.List;
import java.util.function.Supplier;

import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.TLCGlobals;
import tlc2.tool.coverage.CostModel;
import tlc2.tool.impl.ModelConfig;
import tlc2.tool.impl.SpecProcessor;
import tlc2.tool.impl.Tool.Mode;
import tlc2.util.Context;
import tlc2.util.ObjLongTable;
import tlc2.util.Vect;
import tlc2.value.IFcnLambdaValue;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import util.FilenameToStream;

public interface ITool extends TraceApp {

	Mode getMode();
	
	/**
	   * This method returns the set of all possible actions of the
	   * spec, and sets the actions field of this object. In fact, we
	   * could simply treat the next predicate as one "giant" action.
	   * But for efficiency, we preprocess the next state predicate by
	   * splitting it into a set of actions for the maximum prefix
	   * of disjunction and existential quantification.
	   */
	Action[] getActions();

	/*
	   * This method returns the set of possible initial states that
	   * satisfies the initial state predicate. Initial state predicate
	   * can be under-specified.  Too many possible initial states will
	   * probably make tools like TLC useless.
	   */
	StateVec getInitStates();

	void getInitStates(IStateFunctor functor);

	/* Create the state specified by pred.  */
	TLCState makeState(SemanticNode pred);

	/**
	   * This method returns the set of next states when taking the action
	   * in the given state.
	   */
	StateVec getNextStates(Action action, TLCState state);
	
	boolean getNextStates(final INextStateFunctor functor, final TLCState state);

	boolean getNextStates(final INextStateFunctor functor, final TLCState state, final Action action);
	
	IValue eval(SemanticNode expr);

	IValue eval(SemanticNode expr, Context c);

	IValue eval(SemanticNode expr, Context c, TLCState s0);

	IValue eval(SemanticNode expr, Context c, TLCState s0, TLCState s1, int control);
	
	IValue eval(SemanticNode expr, Context c, TLCState s0, TLCState s1, int control, CostModel cm);

	/**
	   * This method determines if the argument is a valid state.  A state
	   * is good iff it assigns legal explicit values to all the global
	   * state variables.
	   */
	boolean isGoodState(TLCState state);

	/* This method determines if a state satisfies the model constraints. */
	boolean isInModel(TLCState state) throws EvalException;

	/* This method determines if a pair of states satisfy the action constraints. */
	boolean isInActions(TLCState s1, TLCState s2) throws EvalException;

	boolean hasStateOrActionConstraints();

	/**
	   * This method determines if an action is enabled in the given state.
	   * More precisely, it determines if (act.pred /\ (sub' # sub)) is
	   * enabled in the state s and context act.con.
	   */
	TLCState enabled(SemanticNode pred, Context c, TLCState s0, TLCState s1, ExprNode subscript, final int ail);
	TLCState enabled(SemanticNode pred, Context c, TLCState s0, TLCState s1);
	TLCState enabled(SemanticNode pred, IActionItemList acts, Context c, TLCState s0, TLCState s1);
	TLCState enabled(SemanticNode pred, IActionItemList acts, Context c, TLCState s0, TLCState s1, CostModel cm);

	boolean isValid(ExprNode expr, Context ctxt);
	
	/* This method determines if the action predicate is valid in (s0, s1). */
	boolean isValid(Action act, TLCState s0, TLCState s1);

	/* Returns true iff the predicate is valid in the state. */
	boolean isValid(Action act, TLCState state);

	/* Returns true iff the predicate is valid in the state. */
	boolean isValid(Action act);

	boolean isValid(ExprNode expr);

	/* Reconstruct the initial state whose fingerprint is fp. */
	TLCStateInfo getState(long fp);

	/**
		 * Reconstruct the next state of state s whose fingerprint is fp.
		 *
		 * @return Returns the TLCState wrapped in TLCStateInfo. TLCStateInfo stores
		 *         the stateNumber (relative to the given sinfo) and a pointer to
		 *         the predecessor.
		 */
	TLCStateInfo getState(long fp, TLCStateInfo sinfo);

	/* Reconstruct the next state of state s whose fingerprint is fp. */
	TLCStateInfo getState(long fp, TLCState s);

	/* Reconstruct the info for s1.   */
	TLCStateInfo getState(TLCState s1, TLCState s);

	/* Return the set of all permutations under the symmetry assumption. */
	IMVPerm[] getSymmetryPerms();

	boolean hasSymmetry();

	Context getFcnContext(IFcnLambdaValue fcn, ExprOrOpArgNode[] args, Context c, TLCState s0, TLCState s1, int control);

	Context getFcnContext(IFcnLambdaValue fcn, ExprOrOpArgNode[] args, Context c, TLCState s0, TLCState s1, int control,
			CostModel cm);

	IContextEnumerator contexts(OpApplNode appl, Context c, TLCState s0, TLCState s1, int control);

	Vect<Action> getInitStateSpec();

	Action[] getInvariants();

	ObjLongTable<SemanticNode> getPrimedLocs();

	Context getOpContext(OpDefNode odn, ExprOrOpArgNode[] args, Context ctx, boolean b);

	ExprNode[] getAssumptions();

	boolean[] getAssumptionIsAxiom();

	int checkAssumptions();
	
	int checkPostCondition();
	
	int checkPostConditionWithCounterExample(IValue value);

	String[] getInvNames();

	String[] getImpliedActNames();

	/**
	 * @return The name of the root module.
	 */
	String getRootName();
	
	/**
	 * @return The file name of the root module which might contain the
	 *         full or relative path information.
	 */
	String getRootFile();

	String getConfigFile();

	String getSpecDir();

	String[] getImpliedInitNames();

	/**
	 * Initial predicate of the liveness property Prop (see impliedActions above).
	 * Most common used when checking if a Spec implements another one, i.e. ASpec
	 * => BSpec.
	 * <p>
	 * See the following tests:<br>
	 * tlc2.tool.suite.Test55
	 * <ul>
	 * <li>Action line 7, col 1 to line 7, col 41 of module test55</li>
	 * <li>Action line 7, col 1 to line 7, col 41 of module test55</li>
	 * </ul>
	 * tlc2.tool.suite.Test63
	 * <ul>
	 * <li>Action line 52, col 1 to line 52, col 21 of module test63</li>
	 * </ul>
	 */
	Action[] getImpliedInits();

	/**
	 * Checking a liveness property Prop (declared by the PROPERTY keyword in the
	 * config file) means to verify Spec => Prop. An implied action is the [][A]_x
	 * (A \/ x' = x) part of Prop where A is an action and x is a variable.
	 * 
	 * See the following tests:<br>
	 * tlc2.tool.suite.Test52
	 * <ul>
	 * <li></li>
	 * <li></li>
	 * </ul>
	 * tlc2.tool.suite.Test56
	 * <ul>
	 * <li></li>
	 * </ul>
	 */
	Action[] getImpliedActions();

	boolean livenessIsTrue();

	Action[] getImpliedTemporals();

	Action[] getTemporals();

	Object lookup(SymbolNode opNode, Context con, boolean b);

	Object lookup(SymbolNode operator);

	Object getVal(ExprOrOpArgNode expr, Context con, boolean b);

	Action getNextStateSpec();

	SemanticNode getViewSpec();

	ExprNode[] getPostConditionSpecs();

	OpDefNode getCounterExampleDef();

	int getId();

	List<File> getModuleFiles(FilenameToStream resolver);

	ModelConfig getModelConfig();

	SpecProcessor getSpecProcessor();

	ExprNode[] getActionConstraints();

	ExprNode[] getModelConstraints();

	TLCStateInfo evalAlias(TLCStateInfo current, TLCState successor, Supplier<List<TLCStateInfo>> prefix);

	TLCStateInfo evalAlias(TLCStateInfo curState, TLCState sucState);

	TLCState evalAlias(TLCState curState, TLCState sucState);

	default <T> T eval(Supplier<T> supplier) {
		return supplier.get();
	}

	default ITool getDebugger() {
		if (TLCGlobals.mainChecker != null) {
			return TLCGlobals.mainChecker.tool;
		}
		if (TLCGlobals.simulator != null) {
			return TLCGlobals.simulator.getTool();
		}
		return this;
	}

	default ITool getLiveness() {
		return this;
	}

	default Vect<Action> getSpecActions() {
		return getInitStateSpec().concat(new Vect<Action>(getActions()));
	}
}