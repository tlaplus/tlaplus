///*******************************************************************************
// * Copyright (c) 2018 Microsoft Research. All rights reserved. 
// *
// * The MIT License (MIT)
// * 
// * Permission is hereby granted, free of charge, to any person obtaining a copy 
// * of this software and associated documentation files (the "Software"), to deal
// * in the Software without restriction, including without limitation the rights
// * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
// * of the Software, and to permit persons to whom the Software is furnished to do
// * so, subject to the following conditions:
// *
// * The above copyright notice and this permission notice shall be included in all
// * copies or substantial portions of the Software. 
// * 
// * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
// * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
// * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
// * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
// * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
// *
// * Contributors:
// *   Markus Alexander Kuppe - initial API and implementation
// ******************************************************************************/
//package tlc2.tool;
//
//import tlc2.tool.Action;
//import tlc2.tool.ActionItemList;
//import tlc2.tool.IStateFunctor;
//import tlc2.tool.StateVec;
//import tlc2.tool.TLCState;
//import tlc2.tool.coverage.CostModel;
//import tlc2.util.Context;
//import tlc2.TLCGlobals;
//import tla2sany.semantic.OpApplNode;
//import tla2sany.semantic.SemanticNode;
//
//public final aspect CostModelAspect {
//	
//	// -------------------------------- //
//	
///*
//  private final void getInitStates(ActionItemList acts, TLCState ps, IStateFunctor states, CostModel cm) {
// */
//	
//	final pointcut getInitStates(ActionItemList acts, TLCState ps, IStateFunctor states, CostModel cm): 
//		execution(private void tlc2.tool.Tool.getInitStates(ActionItemList, TLCState, IStateFunctor, CostModel))
//		&& args(acts, ps, states, cm) && !within(CostModelAspect) && if(TLCGlobals.isCoverageEnabled()) ;
//
//	void around(ActionItemList acts, TLCState ps, IStateFunctor states, CostModel cm): (getInitStates(acts, ps, states, cm)) {
//		if (acts.isEmpty() || ps.allAssigned()) {
//			cm.incInvocations();
//			cm.getRoot().incInvocations();
//		}
//		proceed(acts, ps, states, cm);
//	}
//
//	// -------------------------------- //
//	
///*
//  public StateVec getNextStates(Action action, TLCState state) {
//    action.cm.incInvocations(nss.size());
//  }
//*/
//
//	final pointcut getNextStatesAction(Action action, TLCState state): 
//		execution(public tlc2.tool.StateVec tlc2.tool.Tool.getNextStates(Action, TLCState))
//		&& args(action, state) && !within(CostModelAspect) && if(TLCGlobals.isCoverageEnabled());
//
//	//TODO Rewrite to after returning?
//	StateVec around(final Action action, final TLCState state): (getNextStatesAction(action, state)) {
//		final StateVec nss = (StateVec) proceed(action, state);
//		action.cm.incInvocations(nss.size());
//		
//		return nss;
//	}
//
//	// -------------------------------- //
//	
///*
//  private final TLCState getNextStates(ActionItemList acts, final TLCState s0, final TLCState s1, final StateVec nss, CostModel cm) {
//	  final TLCState copy = getNextStates0(acts, s0, s1, nss, cm);
//	  if (copy != s1) {
//		  cm.incInvocations();
//	  }
//	  return copy;
//  }
//*/
//
//	final pointcut getNextStates(ActionItemList acts, TLCState s0, TLCState s1, StateVec nss, CostModel cm): 
//		execution(private tlc2.tool.TLCState tlc2.tool.Tool.getNextStates(ActionItemList, TLCState, TLCState, StateVec, CostModel))
//		&& args(acts, s0, s1, nss, cm) && !within(CostModelAspect) && if(TLCGlobals.isCoverageEnabled());
//
//	TLCState around(ActionItemList acts, TLCState s0, TLCState s1, StateVec nss, CostModel cm): (getNextStates(acts, s0, s1, nss, cm)) {
//		final TLCState copy = (TLCState) proceed(acts, s0, s1, nss, cm);
//		if (copy != s1) {
//			cm.incInvocations();
//		}
//		return copy;
//	}
//
//	// -------------------------------- //
//	
///*
//  private final Value setSource(final SemanticNode expr, final Value value, CostModel cm) {
//    value.setCostModel(cm.get(expr));
//*/
//
//	final pointcut setSource(SemanticNode expr, final Value value, CostModel cm): 
//		execution(private tlc2.value.Value tlc2.tool.Tool.setSource(SemanticNode, Value, CostModel))
//		&& args(expr, value, cm) && !within(CostModelAspect) && if(TLCGlobals.isCoverageEnabled());
//
//	Value around(SemanticNode expr, final Value value, CostModel cm): (setSource(expr, value, cm)) {
//		value.setCostModel(cm.get(expr));
//		return proceed(expr, value, cm);
//	}
//
//	// -------------------------------- //
//	
///*
//	private final Value evalAppl(final OpApplNode expr, Context c, TLCState s0, TLCState s1, final int control, CostModel cm) {
//		cm = cm.get(expr);
//		cm.incInvocations();
//*/
//
//	final pointcut evalsAppl(OpApplNode expr, Context c, TLCState s0, TLCState s1, int control, CostModel cm): 
//		execution(private tlc2.value.Value tlc2.tool.Tool.evalAppl(tla2sany.semantic.OpApplNode, Context, TLCState, TLCState, int, CostModel))
//		&& args(expr, c, s0, s1, control, cm) && !within(CostModelAspect) && if(TLCGlobals.isCoverageEnabled());
//
//	Value around(OpApplNode expr, Context c, TLCState s0, TLCState s1, int control, CostModel cm): (evalsAppl(expr, c, s0, s1, control, cm)) {
//		return proceed(expr, c, s0, s1, control, cm.get(expr).incInvocations());
//	}
//	
//	// -------------------------------- //
//	
///*
//    
//  private final TLCState getNextStates(SemanticNode pred, ActionItemList acts, Context c, TLCState s0, TLCState s1, StateVec nss, CostModel cm) {
//    cm = cm.get(pred);
//    
//  private final TLCState processUnchanged(SemanticNode expr, ActionItemList acts, Context c, TLCState s0, TLCState s1, StateVec nss, CostModel cm) {
//    cm = cm.get(expr);
//*/
//
//	final pointcut evals6(SemanticNode expr, ActionItemList acts, Context c, TLCState s0, TLCState s1, StateVec nss,
//			CostModel cm): 
//		(execution(private tlc2.tool.TLCState tlc2.tool.Tool.getNextStates(SemanticNode, ActionItemList, Context, TLCState, TLCState, StateVec, CostModel)) ||
//				execution(private tlc2.tool.TLCState tlc2.tool.Tool.processUnchanged(SemanticNode, ActionItemList, Context, TLCState, TLCState, StateVec, CostModel)))
//				&& args(expr, acts, c, s0, s1, nss, cm) && !within(CostModelAspect) && if(TLCGlobals.isCoverageEnabled());
//
//	TLCState around(SemanticNode expr, ActionItemList acts, Context c, TLCState s0, TLCState s1, StateVec nss, CostModel cm): (evals6(expr, acts, c, s0, s1, nss, cm)) {
//		return proceed(expr, acts, c, s0, s1, nss, cm.get(expr));
//	}
//	
//	// -------------------------------- //
//	
///*
//  private final void getInitStatesAppl(OpApplNode init, ActionItemList acts, Context c, TLCState ps, IStateFunctor states, CostModel cm) {
//    cm = cm.get(init);
//*/
//	
//	final pointcut getInitStatesAppl(OpApplNode expr, ActionItemList acts, Context c, TLCState ps, IStateFunctor states, CostModel cm): 
//				execution(private void tlc2.tool.Tool.getInitStatesAppl(OpApplNode, ActionItemList, Context, TLCState, IStateFunctor, CostModel))
//				&& args(expr, acts, c, ps, states, cm) && !within(CostModelAspect) && if(TLCGlobals.isCoverageEnabled());
//
//	void around(OpApplNode expr, ActionItemList acts, Context c, TLCState ps, IStateFunctor states, CostModel cm): (getInitStatesAppl(expr, acts, c, ps, states, cm)) {
//		proceed(expr, acts, c, ps, states, cm.get(expr));
//	}
//	
//	// -------------------------------- //
//	
///*
//  private final TLCState enabledAppl(OpApplNode pred, ActionItemList acts, Context c, TLCState s0, TLCState s1, CostModel cm) {
//    cm = cm.get(pred);
//*/
//	
//	final pointcut enableAppl(OpApplNode expr, ActionItemList acts, Context c, TLCState s0, TLCState s1, CostModel cm): 
//				execution(private tlc2.tool.TLCState tlc2.tool.Tool.enabledAppl(OpApplNode, ActionItemList, Context, TLCState, TLCState, CostModel))
//		&& args(expr, acts, c, s0, s1, cm) && !within(CostModelAspect) && if(TLCGlobals.isCoverageEnabled());
//
//	TLCState around(OpApplNode expr, ActionItemList acts, Context c, TLCState s0, TLCState s1, CostModel cm): (enableAppl(expr, acts, c, s0, s1, cm)) {
//		return proceed(expr, acts, c, s0, s1, cm.get(expr));
//	}
//	
//	// -------------------------------- //
//	
///*
//  public final Value eval(SemanticNode expr, Context c, TLCState s0, TLCState s1, final int control, CostModel cm) {
//	 cm = cm.get(expr)
//*/
//	
//	final pointcut eval(SemanticNode expr, Context c, TLCState s0, TLCState s1, int control, CostModel cm): 
//		execution(public tlc2.value.Value tlc2.tool.Tool.eval(SemanticNode, Context, TLCState, TLCState, int, CostModel))
//			&& args(expr, c, s0, s1, control, cm) && !within(CostModelAspect) && if(TLCGlobals.isCoverageEnabled());
//
//	Value around(SemanticNode expr, Context c, TLCState s0, TLCState s1, int control, CostModel cm): (eval(expr, c, s0, s1, control, cm)) {
//		return proceed(expr, c, s0, s1, control, cm.get(expr));
//	}
//
//	// ---------------- Pass on CostModel instances from existing Value to newly instantiated ones. ---------------- //
//	
//	final pointcut newValueCtor() : call(tlc2.value.Value+.new(..)) && !within(CostModelAspect) && if(TLCGlobals.isCoverageEnabled());
//	
//	after() returning(final Value newValue) : newValueCtor() {
//		if (thisJoinPoint.getThis() instanceof Value) {
//			// Get CostModel instance from existing Value and attach to new one.
//			final Value existingValue = (Value) thisJoinPoint.getThis();
//			newValue.setCostModel(existingValue.getCostModel());
//		}
//	}
//
//	// ---------------- (Finally) count invocations to ValueEnumerator#elements to measure costs. ---------------- //
//
//	final pointcut elementsExec(Enumerable en): 
//		execution(public tlc2.value.ValueEnumeration tlc2.value.Enumerable+.elements(..))
//		&& target(en) && !within(CostModelAspect) && if(TLCGlobals.isCoverageEnabled());
//
//	ValueEnumeration around(Enumerable en): (elementsExec(en)) {
//		return new WrappingValueEnumeration(((Enumerable) en).getCostModel(), (ValueEnumeration) proceed(en));
//	}
//
//	private static class WrappingValueEnumeration implements ValueEnumeration {
//
//		private final CostModel cm;
//		private final ValueEnumeration ve;
//		
//		public WrappingValueEnumeration(CostModel costModel, ValueEnumeration ve) {
//			this.cm = costModel.incInvocations(1);
//			this.ve = ve;
//		}
//
//		@Override
//		public void reset() {
//			ve.reset();
//		}
//
//		@Override
//		public Value nextElement() {
//			cm.incSecondary();
//			return ve.nextElement();
//		}
//	}
//}
