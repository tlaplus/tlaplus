// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2022, Oracle and/or its affiliates.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Thu  2 Aug 2007 at 10:25:48 PST by lamport
//      modified on Fri Jan  4 22:46:57 PST 2002 by yuanyu

package tlc2.tool.impl;

import java.io.File;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.APSubstInNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LabelNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.LevelConstants;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.OpDefOrDeclNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.Action;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.IActionItemList;
import tlc2.tool.IContextEnumerator;
import tlc2.tool.INextStateFunctor;
import tlc2.tool.IStateFunctor;
import tlc2.tool.ITool;
import tlc2.tool.StateVec;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateFun;
import tlc2.tool.TLCStateInfo;
import tlc2.tool.TLCStateMut;
import tlc2.tool.TLCStateMutExt;
import tlc2.tool.ToolGlobals;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.util.ExpectInlined;
import tlc2.util.IdThread;
import tlc2.util.RandomGenerator;
import tlc2.util.Vect;
import tlc2.value.IFcnLambdaValue;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.ValueConstants;
import tlc2.value.Values;
import tlc2.value.impl.Applicable;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.Enumerable;
import tlc2.value.impl.Enumerable.Ordering;
import tlc2.value.impl.EvaluatingValue;
import tlc2.value.impl.FcnLambdaValue;
import tlc2.value.impl.FcnParams;
import tlc2.value.impl.FcnRcdValue;
import tlc2.value.impl.LazySupplierValue;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.MVPerm;
import tlc2.value.impl.MVPerms;
import tlc2.value.impl.MethodValue;
import tlc2.value.impl.ModelValue;
import tlc2.value.impl.OpLambdaValue;
import tlc2.value.impl.OpValue;
import tlc2.value.impl.RecordValue;
import tlc2.value.impl.Reducible;
import tlc2.value.impl.SetCapValue;
import tlc2.value.impl.SetCupValue;
import tlc2.value.impl.SetDiffValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.SetOfFcnsValue;
import tlc2.value.impl.SetOfRcdsValue;
import tlc2.value.impl.SetOfTuplesValue;
import tlc2.value.impl.SetPredValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.SubsetValue;
import tlc2.value.impl.TupleValue;
import tlc2.value.impl.UnionValue;
import tlc2.value.impl.Value;
import tlc2.value.impl.ValueEnumeration;
import tlc2.value.impl.ValueExcept;
import tlc2.value.impl.ValueVec;
import util.Assert;
import util.Assert.TLCRuntimeException;
import util.FilenameToStream;
import util.TLAConstants;
import util.UniqueString;

/**
 * This class provides useful methods for tools like model checker
 * and simulator.
 *
 * It's instance serves as a spec handle
 * This is one of two places in TLC, where not all messages are retrieved from the message printer,
 * but constructed just here in the code.
 */
public abstract class Tool
    extends Spec
    implements ValueConstants, ToolGlobals, ITool
{

  	public static final String PROBABILISTIC_KEY = Tool.class.getName() + ".probabilistic";
    /*
	 * Prototype, do *not* activate when checking safety or liveness!!!:
	 * For simulation that is not meant as a substitute of exhaustive checking for too
	 * large models, it can be useful to generate behaviors as quickly as possible,
	 * i.e. without checking all successor states along the states of the behavior.
	 * This flag activates the code path that efficiently generate only a single 
	 * successor state during simulation.  It does not let the user parameterize
	 * the code with a particular distribution, but instead draws from the uniform
	 * distribution.  
	 * 
	 * In its current form, it only handles non-determinism expressed with opcode
	 * OPCODE_be (bounded exist), i.e. (which simply happened to be the primary
	 * expression that we encountered in the SWIM spec during this work):
	 * 
	 * VARIABLE x
	 * \E n \in S: x' = n
	 * 
	 * Activate with: -Dtlc2.tool.impl.Tool.probabilistic=true
	 */
  private static final boolean PROBABILISTIC = Boolean.getBoolean(PROBABILISTIC_KEY);

  public enum Mode {
	  Simulation, MC, MC_DEBUG, Executor;
  }
	
  public static final Value[] EmptyArgs = new Value[0];

  protected final Action[] actions;     // the list of TLA actions.
  private Vect<Action> actionVec = new Vect<>(10);
  protected final Mode toolMode;

  /**
   * Creates a new tool handle
   */
  public Tool(String specFile, String configFile) {
	  this(new File(specFile), specFile, configFile, null);
  }
  
  public Tool(String specFile, String configFile, FilenameToStream resolver) {
	  this(new File(specFile), specFile, configFile, resolver);
  }
  
  public Tool(String specFile, String configFile, FilenameToStream resolver, final Map<String, Object> params) {
	  this(new File(specFile), specFile, configFile, resolver, params);
  }

  public Tool(String specFile, String configFile, FilenameToStream resolver, Mode mode, final Map<String, Object> params) {
	  this(new File(specFile), specFile, configFile, resolver, mode, params);
  }
  
  private Tool(File specDir, String specFile, String configFile, FilenameToStream resolver)
  {
	  this(specDir.isAbsolute() ? specDir.getParent() : "", specFile, configFile, resolver, new HashMap<>());
  }
  
  private Tool(File specDir, String specFile, String configFile, FilenameToStream resolver, final Map<String, Object> params)
  {
	  this(specDir.isAbsolute() ? specDir.getParent() : "", specFile, configFile, resolver, params);
  }
  
  private Tool(File specDir, String specFile, String configFile, FilenameToStream resolver, Mode mode, final Map<String, Object> params)
  {
	  this(specDir.isAbsolute() ? specDir.getParent() : "", specFile, configFile, resolver, mode, params);
  }
  
  public Tool(String specDir, String specFile, String configFile, FilenameToStream resolver, final Map<String, Object> params)
  {
	  this(specDir, specFile, configFile, resolver, Mode.MC, params);
  }
  
  public Tool(String specDir, String specFile, String configFile, FilenameToStream resolver, Mode mode, final Map<String, Object> params)
  {
      super(specDir, specFile, configFile, resolver, mode, params);

      this.toolMode = mode;
		// set variables to the static filed in the state
		if (mode == Mode.Simulation || mode == Mode.Executor || mode == Mode.MC_DEBUG) {
			assert TLCState.Empty instanceof TLCStateMutExt;
			TLCStateMutExt.setTool(this);
		} else {
			// Initialize state.
			assert TLCState.Empty instanceof TLCStateMut;
			TLCStateMut.setTool(this);
		}
      
		Action next = this.getNextStateSpec();
		if (next == null) {
			this.actions = new Action[0];
		} else {
			this.getActions(next);
			int sz = this.actionVec.size();
			this.actions = new Action[sz];
			for (int i = 0; i < sz; i++) {
				this.actions[i] = (Action) this.actionVec.elementAt(i);
			}
		}
		
		// Tag the initial predicates and next-state actions.
		final Vect<Action> initAndNext = getInitStateSpec().concat(actionVec);
		for (int i = 0; i < initAndNext.size(); i++) {
			initAndNext.elementAt(i).setId(i);
		}
  }

  Tool(Tool other) {
	  super(other);
	  this.actions = other.actions;
	  this.actionVec = other.actionVec;
	  this.toolMode = other.toolMode;
  }

  @Override
  public Mode getMode() {
	  return this.toolMode;
  }
  
	/**
   * This method returns the set of all possible actions of the
   * spec, and sets the actions field of this object. In fact, we
   * could simply treat the next predicate as one "giant" action.
   * But for efficiency, we preprocess the next state predicate by
   * splitting it into a set of actions for the maximum prefix
   * of disjunction and existential quantification.
   */
  @Override
  public final Action[] getActions() {
    return this.actions;
  }

	private final void getActions(final Action next) {
		this.getActions(next.pred, next.con, next.getOpDef(), next.cm);
	}

  private final void getActions(SemanticNode next, Context con, final OpDefNode opDefNode, CostModel cm) {
    switch (next.getKind()) {
    case OpApplKind:
      {
        OpApplNode next1 = (OpApplNode)next;
        this.getActionsAppl(next1, con, opDefNode, cm);
        return;
      }
    case LetInKind:
      {
        LetInNode next1 = (LetInNode)next;
        this.getActions(next1.getBody(), con, opDefNode, cm);
        return;
      }
    case SubstInKind:
      {
        SubstInNode next1 = (SubstInNode)next;
        Subst[] substs = next1.getSubsts();
        if (substs.length == 0) {
          this.getActions(next1.getBody(), con, opDefNode, cm);
        }
        else {
          Action action = new Action(next1, con, opDefNode);
          this.actionVec.addElement(action);
        }
        return;
      }

      // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
      case APSubstInKind:
        {
          APSubstInNode next1 = (APSubstInNode)next;
          Subst[] substs = next1.getSubsts();
          if (substs.length == 0) {
            this.getActions(next1.getBody(), con, opDefNode, cm);
          }
          else {
            Action action = new Action(next1, con, opDefNode);
            this.actionVec.addElement(action);
          }
          return;
        }

    /***********************************************************************
    * LabelKind class added by LL on 13 Jun 2007.                          *
    ***********************************************************************/
    case LabelKind:
      {
        LabelNode next1 = (LabelNode)next;
        this.getActions(next1.getBody(), con, opDefNode, cm);
        return;
      }
    default:
      {
        Assert.fail("The next state relation is not a boolean expression.\n" + next, next, con);
      }
    }
  }

  private final void getActionsAppl(OpApplNode next, Context con, final OpDefNode actionName, CostModel cm) {
    ExprOrOpArgNode[] args = next.getArgs();
    SymbolNode opNode = next.getOperator();
    int opcode = BuiltInOPs.getOpCode(opNode.getName());

    if (opcode == 0) {
      Object val = this.lookup(opNode, con, false);

      if (val instanceof OpDefNode) {
        OpDefNode opDef = (OpDefNode)val;
        opcode = BuiltInOPs.getOpCode(opDef.getName());
        if (opcode == 0) {
          try {
            FormalParamNode[] formals = opDef.getParams();
            int alen = args.length;
            int argLevel = 0;
            for (int i = 0; i < alen; i++) {
              argLevel = args[i].getLevel();
              if (argLevel != 0) break;
            }
            if (argLevel == 0) {
              Context con1 = con;
              for (int i = 0; i < alen; i++) {
                IValue aval = this.eval(args[i], con, TLCState.Empty, cm);
                con1 = con1.cons(formals[i], aval);
              }
              this.getActions(opDef.getBody(), con1, opDef, cm);
              return;
            }
          }
          catch (Throwable e) { /*SKIP*/ }
        }
      }
      if (opcode == 0) {
        Action action = new Action(next, con, (OpDefNode) opNode);
        this.actionVec.addElement(action);
        return;
      }
    }

    switch (opcode) {
    case OPCODE_be:     // BoundedExists
      {
        final int cnt = this.actionVec.size();
        try {
          ContextEnumerator Enum =
            this.contexts(next, con, TLCState.Empty, TLCState.Empty, EvalControl.Clear, cm);
          if (Enum.isDone()) {
        	  // No exception and no actions created implies Enum was empty:
        	  // \E i \in {} : ...
        	  // \E i \in Nat: FALSE
        	  // ...
        	  this.actionVec.addElement(new Action(next, con, actionName));
        	  return;
          }
          Context econ;
          while ((econ = Enum.nextElement()) != null) {
            this.getActions(args[0], econ, actionName, cm);
          }
			assert (cnt < this.actionVec.size())
					: "AssertionError when creating Actions. This case should have been handled by Enum.isDone conditional above!";
        }
        catch (Throwable e) {
          Action action = new Action(next, con, actionName);
          this.actionVec.removeAll(cnt);
          this.actionVec.addElement(action);
        }
        return;
      }
    case OPCODE_dl:     // DisjList
    case OPCODE_lor:
      {
        for (int i = 0; i < args.length; i++) {
          this.getActions(args[i], con, actionName, cm);
        }
        return;
      }
    default:
      {
        // We handle all the other builtin operators here.
        Action action = new Action(next, con, actionName);
        this.actionVec.addElement(action);
        return;
      }
    }
  }

  /*
   * This method returns the set of possible initial states that
   * satisfies the initial state predicate. Initial state predicate
   * can be under-specified.  Too many possible initial states will
   * probably make tools like TLC useless.
   */
  @Override
  public final StateVec getInitStates() {
	  final StateVec initStates = new StateVec(0);
	  getInitStates(initStates);
	  return initStates;
  }

  @Override
  public final void getInitStates(IStateFunctor functor) {
	  Vect<Action> init = this.getInitStateSpec();
	  ActionItemList acts = ActionItemListExt.Empty;
      // MAK 09/11/2018: Tail to head iteration order cause the first elem added with
      // acts.cons to be acts tail. This fixes the bug/funny behavior that the init
      // predicate Init == A /\ B /\ C /\ D was evaluated in the order A, D, C, B (A
      // doesn't get added to acts at all).
	  for (int i = (init.size() - 1); i > 0; i--) {
		  Action elem = (Action)init.elementAt(i);
		  acts = (ActionItemList) acts.cons(elem, IActionItemList.PRED);
	  }
	  if (init.size() != 0) {
		  Action elem = (Action)init.elementAt(0);
		  TLCState ps = TLCState.Empty.createEmpty();
		  if (acts.isEmpty()) {
			  acts.setAction(elem);
		  }
		  this.getInitStates(elem.pred, acts, elem.con, ps, functor, elem.cm);
	  }
  }

  /* Create the state specified by pred.  */
  @Override
  public final TLCState makeState(SemanticNode pred) {
    ActionItemList acts = ActionItemList.Empty;
    TLCState ps = TLCState.Empty.createEmpty();
    StateVec states = new StateVec(0);
    this.getInitStates(pred, acts, Context.Empty, ps, states, acts.cm);
    if (states.size() != 1) {
      Assert.fail("The predicate does not specify a unique state." + pred, pred);
    }
    TLCState state = states.elementAt(0);
    if (!this.isGoodState(state)) {
      Assert.fail("The state specified by the predicate is not complete." + pred, pred);
    }
    return state;
  }

  protected void getInitStates(SemanticNode init, ActionItemList acts,
                                   Context c, TLCState ps, IStateFunctor states, CostModel cm) {
        switch (init.getKind()) {
        case OpApplKind:
          {
            OpApplNode init1 = (OpApplNode)init;
            this.getInitStatesAppl(init1, acts, c, ps, states, cm);
            return;
          }
        case LetInKind:
          {
            LetInNode init1 = (LetInNode)init;
            this.getInitStates(init1.getBody(), acts, c, ps, states, cm);
            return;
          }
        case SubstInKind:
          {
            SubstInNode init1 = (SubstInNode)init;
            Subst[] subs = init1.getSubsts();
            Context c1 = c;
            for (int i = 0; i < subs.length; i++) {
              Subst sub = subs[i];
              c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, coverage ? sub.getCM() : cm, toolId));
            }
            this.getInitStates(init1.getBody(), acts, c1, ps, states, cm);
            return;
          }
        // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
        case APSubstInKind:
          {
            APSubstInNode init1 = (APSubstInNode)init;
            Subst[] subs = init1.getSubsts();
            Context c1 = c;
            for (int i = 0; i < subs.length; i++) {
              Subst sub = subs[i];
              c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, cm, toolId));
            }
            this.getInitStates(init1.getBody(), acts, c1, ps, states, cm);
            return;
          }
        // LabelKind class added by LL on 13 Jun 2007
        case LabelKind:
          {
            LabelNode init1 = (LabelNode)init;
            this.getInitStates(init1.getBody(), acts, c, ps, states, cm);
            return;
          }
        default:
          {
            Assert.fail("The init state relation is not a boolean expression.\n" + init, init, c);
          }
        }
  }

  protected void getInitStates(ActionItemList acts, TLCState ps, IStateFunctor states, CostModel cm) {
		if (acts.isEmpty()) {
			if (coverage) {
				cm.incInvocations();
				cm.getRoot().incInvocations();
			}
			states.addElement(ps.copy().setAction(acts.getAction()));
			return;
		} else if (ps.allAssigned()) {
			// MAK 05/25/2018: If all values of the initial state have already been
			// assigned, there is no point in further trying to assign values. Instead, all
			// remaining statements (ActionItemList) can just be evaluated for their boolean
			// value.
			// This optimization is especially useful to check inductive invariants which
			// require TLC to generate a very large set of initial states.
			while (!acts.isEmpty()) {
				final Value bval = this.eval(acts.carPred(), acts.carContext(), ps, TLCState.Empty, EvalControl.Init, acts.cm);
				if (!(bval instanceof BoolValue)) {
					//TODO Choose more fitting error message.
					Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING,
							new String[] { "initial states", "boolean", bval.toString(), acts.pred.toString() }, acts.carPred(), acts.carContext());
				}
				if (!((BoolValue) bval).val) {
					if (coverage) {
						// Increase "states found".
						cm.getRoot().incSecondary();
					}
					return;
				}
				// Move on to the next action in the ActionItemList.
				acts = acts.cdr();
			}
			if (coverage) {
				cm.incInvocations();
				cm.getRoot().incInvocations();
			}
			states.addElement(ps.copy().setAction(acts.getAction()));
			return;
		}
		// Assert.check(act.kind > 0 || act.kind == -1);
		ActionItemList acts1 = acts.cdr();
		this.getInitStates(acts.carPred(), acts1, acts.carContext(), ps, states, acts.cm);
	  }

  protected void getInitStatesAppl(OpApplNode init, ActionItemList acts,
                                       Context c, TLCState ps, IStateFunctor states, CostModel cm) {
    if (coverage) {cm = cm.get(init);}
        ExprOrOpArgNode[] args = init.getArgs();
        int alen = args.length;
        SymbolNode opNode = init.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        if (opcode == 0) {
          // This is a user-defined operator with one exception: it may
          // be substed by a builtin operator. This special case occurs
          // when the lookup returns an OpDef with opcode # 0.
          Object val = this.lookup(opNode, c, ps, false);

          if (val instanceof OpDefNode) {
            OpDefNode opDef = (OpDefNode)val;
            opcode = BuiltInOPs.getOpCode(opDef.getName());
            if (opcode == 0) {
              // Context c1 = this.getOpContext(opDef, args, c, false);
              Context c1 = this.getOpContext(opDef, args, c, true, cm, toolId);
              this.getInitStates(opDef.getBody(), acts, c1, ps, states, cm);
              return;
            }
          }
          // Added 13 Nov 2009 by LL to fix Yuan's fix.
          /*********************************************************************
          * Modified on 23 October 2012 by LL to work if ThmOrAssumpDefNode    *
          * imported with parameterized instantiation.                         *
          *********************************************************************/
          if (val instanceof ThmOrAssumpDefNode) {
            ThmOrAssumpDefNode opDef = (ThmOrAssumpDefNode)val;
            opcode = BuiltInOPs.getOpCode(opDef.getName());
            Context c1 = this.getOpContext(opDef, args, c, true);
            this.getInitStates(opDef.getBody(), acts, c1, ps, states, cm);
            return;
          }

          if (val instanceof LazyValue) {
            LazyValue lv = (LazyValue)val;
            if (lv.getValue() == null || lv.isUncachable()) {
              this.getInitStates(lv.expr, acts, lv.con, ps, states, cm);
              return;
            }
            val = lv.getValue();
          }

          Object bval = val;
          if (alen == 0) {
            if (val instanceof MethodValue) {
              bval = ((MethodValue)val).apply(EmptyArgs, EvalControl.Init);
            } else if (val instanceof EvaluatingValue) {
              // Allow EvaluatingValue overwrites to have zero arity.
              bval = ((EvaluatingValue) val).eval(this, args, c, ps, TLCState.Empty, EvalControl.Init, cm);
            }
          }
          else {
            if (val instanceof OpValue) {
          	  bval = ((OpValue) val).eval(this, args, c, ps, TLCState.Empty, EvalControl.Init, cm);
            }
          }

          if (opcode == 0)
          {
            if (!(bval instanceof BoolValue))
            {
              Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[] { "initial states", "boolean",
                        bval.toString(), init.toString() }, init, c);
            }
            if (((BoolValue) bval).val)
            {
              this.getInitStates(acts, ps, states, cm);
            }
            return;
          }
        }

        switch (opcode) {
        case OPCODE_dl:     // DisjList
        case OPCODE_lor:
          {
            for (int i = 0; i < alen; i++) {
              this.getInitStates(args[i], acts, c, ps, states, cm);
            }
            return;
          }
        case OPCODE_cl:     // ConjList
        case OPCODE_land:
          {
            for (int i = alen-1; i > 0; i--) {
              acts = (ActionItemList) acts.cons(args[i], c, cm, i);
            }
            this.getInitStates(args[0], acts, c, ps, states, cm);
            return;
          }
        case OPCODE_be:     // BoundedExists
          {
            SemanticNode body = args[0];
            ContextEnumerator Enum = this.contexts(init, c, ps, TLCState.Empty, EvalControl.Init, cm);
            Context c1;
            while ((c1 = Enum.nextElement()) != null) {
              this.getInitStates(body, acts, c1, ps, states, cm);
            }
            return;
          }
        case OPCODE_bf:     // BoundedForall
          {
            SemanticNode body = args[0];
            ContextEnumerator Enum = this.contexts(init, c, ps, TLCState.Empty, EvalControl.Init, cm);
            Context c1 = Enum.nextElement();
            if (c1 == null) {
              this.getInitStates(acts, ps, states, cm);
            }
            else {
              ActionItemList acts1 = acts;
              Context c2;
              while ((c2 = Enum.nextElement()) != null) {
                acts1 = (ActionItemList) acts1.cons(body, c2, cm, IActionItemList.PRED);
              }
              this.getInitStates(body, acts1, c1, ps, states, cm);
            }
            return;
          }
        case OPCODE_ite:    // IfThenElse
          {
            Value guard = this.eval(args[0], c, ps, TLCState.Empty, EvalControl.Init, cm);
            if (!(guard instanceof BoolValue)) {
              Assert.fail("In computing initial states, a non-boolean expression (" +
                          guard.getKindString() + ") was used as the condition " +
                          "of an IF.\n" + init, init, c);
            }
            int idx = (((BoolValue)guard).val) ? 1 : 2;
            this.getInitStates(args[idx], acts, c, ps, states, cm);
            return;
          }
        case OPCODE_case:   // Case
          {
            SemanticNode other = null;
            for (int i = 0; i < alen; i++) {
              OpApplNode pair = (OpApplNode)args[i];
              ExprOrOpArgNode[] pairArgs = pair.getArgs();
              if (pairArgs[0] == null) {
                other = pairArgs[1];
              }
              else {
                Value bval = this.eval(pairArgs[0], c, ps, TLCState.Empty, EvalControl.Init, cm);
                if (!(bval instanceof BoolValue)) {
                  Assert.fail("In computing initial states, a non-boolean expression (" +
                              bval.getKindString() + ") was used as a guard condition" +
                              " of a CASE.\n" + pairArgs[1], pairArgs[1], c);
                }
                if (((BoolValue)bval).val) {
                  this.getInitStates(pairArgs[1], acts, c, ps, states, cm);
                  return;
                }
              }
            }
            if (other == null) {
              Assert.fail("In computing initial states, TLC encountered a CASE with no" +
                          " conditions true.\n" + init, init, c);
            }
            this.getInitStates(other, acts, c, ps, states, cm);
            return;
          }
        case OPCODE_fa:     // FcnApply
          {
            Value fval = this.eval(args[0], c, ps, TLCState.Empty, EvalControl.Init, cm);
            if (fval instanceof FcnLambdaValue) {
              FcnLambdaValue fcn = (FcnLambdaValue)fval;
              if (fcn.fcnRcd == null) {
                Context c1 = this.getFcnContext(fcn, args, c, ps, TLCState.Empty, EvalControl.Init, cm);
                this.getInitStates(fcn.body, acts, c1, ps, states, cm);
                return;
              }
              fval = fcn.fcnRcd;
            }
            else if (!(fval instanceof Applicable)) {
              Assert.fail("In computing initial states, a non-function (" +
                          fval.getKindString() + ") was applied as a function.\n" + init, init, c);
            }
            Applicable fcn = (Applicable) fval;
            Value argVal = this.eval(args[1], c, ps, TLCState.Empty, EvalControl.Init, cm);
            Value bval = fcn.apply(argVal, EvalControl.Init);
            if (!(bval instanceof BoolValue))
            {
              Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING2, new String[] { "initial states", "boolean",
                      init.toString() }, args[1], c);
            }
            if (((BoolValue)bval).val) {
              this.getInitStates(acts, ps, states, cm);
            }
            return;
          }
        case OPCODE_eq:
          {
            SymbolNode var = this.getVar(args[0], c, false, toolId);
            if (var == null || var.getName().getVarLoc() < 0) {
              Value bval = this.eval(init, c, ps, TLCState.Empty, EvalControl.Init, cm);
              if (!((BoolValue)bval).val) {
                return;
              }
            }
            else {
              UniqueString varName = var.getName();
              IValue lval = ps.lookup(varName);
              Value rval = this.eval(args[1], c, ps, TLCState.Empty, EvalControl.Init, cm);
              if (lval == null) {
                ps = ps.bind(varName, rval);
                this.getInitStates(acts, ps, states, cm);
                ps.unbind(varName);
                return;
              }
              else {
                if (!lval.equals(rval)) {
                  return;
                }
              }
            }
            this.getInitStates(acts, ps, states, cm);
            return;
          }
        case OPCODE_in:
          {
            SymbolNode var = this.getVar(args[0], c, false, toolId);
            if (var == null || var.getName().getVarLoc() < 0) {
              Value bval = this.eval(init, c, ps, TLCState.Empty, EvalControl.Init, cm);
              if (!((BoolValue)bval).val) {
                return;
              }
            }
            else {
              UniqueString varName = var.getName();
              Value lval = (Value) ps.lookup(varName);
              Value rval = this.eval(args[1], c, ps, TLCState.Empty, EvalControl.Init, cm);
              if (lval == null) {
                if (!(rval instanceof Enumerable)) {
                  Assert.fail("In computing initial states, the right side of \\IN" +
                              " is not enumerable.\n" + init, init, c);
                }
                ValueEnumeration Enum = ((Enumerable)rval).elements();
                Value elem;
                while ((elem = Enum.nextElement()) != null) {
                  ps.bind(varName, elem);
                  this.getInitStates(acts, ps, states, cm);
                  ps.unbind(varName);
                }
                return;
              }
              else {
                if (!rval.member(lval)) {
                  return;
                }
              }
            }
            this.getInitStates(acts, ps, states, cm);
            return;
          }
        case OPCODE_implies:
          {
            Value lval = this.eval(args[0], c, ps, TLCState.Empty, EvalControl.Init, cm);
            if (!(lval instanceof BoolValue)) {
              Assert.fail("In computing initial states of a predicate of form" +
                          " P => Q, P was " + lval.getKindString() + "\n." + init, init, c);
            }
            if (((BoolValue)lval).val) {
              this.getInitStates(args[1], acts, c, ps, states, cm);
            }
            else {
              this.getInitStates(acts, ps, states, cm);
            }
            return;
          }
        // The following case added by LL on 13 Nov 2009 to handle subexpression names.
        case OPCODE_nop:
        {
           this.getInitStates(args[0], acts, c, ps, states, cm);
           return;
        }
        default:
          {
            // For all the other builtin operators, simply evaluate:
            Value bval = this.eval(init, c, ps, TLCState.Empty, EvalControl.Init, cm);
            if (!(bval instanceof BoolValue)) {

              Assert.fail("In computing initial states, TLC expected a boolean expression," +
                          "\nbut instead found " + bval + ".\n" + init, init, c);
            }
            if (((BoolValue)bval).val) {
              this.getInitStates(acts, ps, states, cm);
            }
            return;
          }
        }
  }
  
  /**
   * This method returns the set of next states when taking the action
   * in the given state.
   */
  @Override
  public final StateVec getNextStates(Action action, TLCState state) {
	  return getNextStates(action, action.con, state);
  }
  
  public final StateVec getNextStates(final Action action, final Context ctx, final TLCState state) {
    ActionItemList acts = ActionItemList.Empty;
    TLCState s1 = TLCState.Empty.createEmpty();
    StateVec nss = new StateVec(0);
    this.getNextStates(action, action.pred, acts, ctx, state, s1.setPredecessor(state).setAction(action), nss, action.cm);
    if (coverage) { action.cm.incInvocations(nss.size()); }
    if (PROBABILISTIC && nss.size() > 1) {System.err.println("Simulator generated more than one next state");}
    return nss;
  }
  
  @Override
  public boolean getNextStates(final INextStateFunctor functor, final TLCState state) {
	  for (int i = 0; i < actions.length; i++) {
			this.getNextStates(functor, state, actions[i]);
		}
		return false;
  }

  public boolean getNextStates(final INextStateFunctor functor, final TLCState state, final Action action) {
		this.getNextStates(action, action.pred, ActionItemList.Empty, action.con, state,
				TLCState.Empty.createEmpty().setPredecessor(state).setAction(action), functor, action.cm);
		return false;
  }
  
  protected abstract TLCState getNextStates(final Action action, SemanticNode pred, ActionItemList acts, Context c,
                                       TLCState s0, TLCState s1, INextStateFunctor nss, CostModel cm);
  
  protected final TLCState getNextStatesImpl(final Action action, SemanticNode pred, ActionItemList acts, Context c,
              TLCState s0, TLCState s1, INextStateFunctor nss, CostModel cm) {
        switch (pred.getKind()) {
        case OpApplKind:
          {
            OpApplNode pred1 = (OpApplNode)pred;
            if (coverage) {cm = cm.get(pred);}
            return this.getNextStatesAppl(action, pred1, acts, c, s0, s1, nss, cm);
          }
        case LetInKind:
          {
            LetInNode pred1 = (LetInNode)pred;
            return this.getNextStates(action, pred1.getBody(), acts, c, s0, s1, nss, cm);
          }
        case SubstInKind:
          {
            return getNextStatesImplSubstInKind(action, (SubstInNode) pred, acts, c, s0, s1, nss, cm);
          }
        // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
        case APSubstInKind:
          {
            return getNextStatesImplApSubstInKind(action, (APSubstInNode) pred, acts, c, s0, s1, nss, cm);
          }
        // LabelKind class added by LL on 13 Jun 2007
        case LabelKind:
          {
            LabelNode pred1 = (LabelNode)pred;
            return this.getNextStates(action, pred1.getBody(), acts, c, s0, s1, nss, cm);
          }
        default:
          {
            Assert.fail("The next state relation is not a boolean expression.\n" + pred, pred, c);
          }
        }
    	return s1;
  }

  @ExpectInlined
  private final TLCState getNextStatesImplSubstInKind(final Action action, SubstInNode pred1, ActionItemList acts, Context c, TLCState s0, TLCState s1, INextStateFunctor nss, final CostModel cm) {
  	Subst[] subs = pred1.getSubsts();
  	int slen = subs.length;
  	Context c1 = c;
  	for (int i = 0; i < slen; i++) {
  	  Subst sub = subs[i];
  	  c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, coverage ? sub.getCM() : cm, toolId));
  	}
  	return this.getNextStates(action, pred1.getBody(), acts, c1, s0, s1, nss, cm);
  }
  
  @ExpectInlined
  private final TLCState getNextStatesImplApSubstInKind(final Action action, APSubstInNode pred1, ActionItemList acts, Context c, TLCState s0, TLCState s1, INextStateFunctor nss, final CostModel cm) {
  	Subst[] subs = pred1.getSubsts();
  	int slen = subs.length;
  	Context c1 = c;
  	for (int i = 0; i < slen; i++) {
  	  Subst sub = subs[i];
  	  c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, cm, toolId));
  	}
  	return this.getNextStates(action, pred1.getBody(), acts, c1, s0, s1, nss, cm);
  }
  
  @ExpectInlined
  private final TLCState getNextStates(final Action action, ActionItemList acts, final TLCState s0, final TLCState s1,
          final INextStateFunctor nss, CostModel cm) {
	  final TLCState copy = getNextStates0(action, acts, s0, s1, nss, cm);
	  if (coverage && copy != s1) {
		  cm.incInvocations();
	  }
	  return copy;
  }

  
  @ExpectInlined
  private final TLCState getNextStates0(final Action action, ActionItemList acts, final TLCState s0, final TLCState s1,
                                       final INextStateFunctor nss, CostModel cm) {
    if (acts.isEmpty()) {
      nss.addElement(s0, action, s1);
      return s1.copy();
    } else if (TLCGlobals.warn && s1.allAssigned()) {
		// If all variables have been assigned and warnings are turned off, Tool can
		// execute the fast-path that avoids generating known successor states, but
		// doesn't trigger a warning in cases like:
    	//  ---- MODULE F ----
    	//  VARIABLES x
    	//  Init == x = 0
    	//  Next == x' = 42 /\ UNCHANGED x \* UNCHANGED and changed!
    	//  ====
    	// => "Warning: The variable x was changed while it is specified as UNCHANGED"
    	return getNextStatesAllAssigned(action, acts, s0, s1, nss, cm);
    }

    final int kind = acts.carKind();
    SemanticNode pred = acts.carPred();
    Context c = acts.carContext();
    ActionItemList acts1 = acts.cdr();
    cm = acts.cm;
    if (kind > 0) {
      return this.getNextStates(action, pred, acts1, c, s0, s1, nss, cm);
    }
    else if (kind == -1) {
      return this.getNextStates(action, pred, acts1, c, s0, s1, nss, cm);
    }
    else if (kind == -2) {
      return this.processUnchanged(action, pred, acts1, c, s0, s1, nss, cm);
    }
    else {
      IValue v1 = this.eval(pred, c, s0, cm);
      IValue v2 = this.eval(pred, c, s1, cm);
      if (!v1.equals(v2)) {
    	  if (coverage) {
    		  return this.getNextStates(action, acts1, s0, s1, nss, cm);
    	  } else {
    		  return this.getNextStates0(action, acts1, s0, s1, nss, cm);
    	  }
      }
    }
    return s1;
  }
  
  private final TLCState getNextStatesAllAssigned(final Action action, ActionItemList acts, final TLCState s0, final TLCState s1,
		  								final INextStateFunctor nss, final CostModel cm) {
	  int kind = acts.carKind();
	  SemanticNode pred = acts.carPred();
	  Context c = acts.carContext();
      CostModel cm2 = acts.cm;
	  while (!acts.isEmpty()) {
		  if (kind > 0 || kind == -1) {
			  final Value bval = this.eval(pred, c, s0, s1, EvalControl.Clear, cm2);
			  if (!(bval instanceof BoolValue)) {
				  // TODO Choose more fitting error message.
				  Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING,
						  new String[] { "next states", "boolean", bval.toString(), acts.pred.toString() }, pred, c);
			  }
			  if (!((BoolValue) bval).val) {
				  return s1;
			  }
		  } else if (kind == -2) {
			  // Identical to default handling below (line 876). Ignored during this optimization.
			  return this.processUnchanged(action, pred, acts.cdr(), c, s0, s1, nss, cm2);
		  } else {
			  final IValue v1 = this.eval(pred, c, s0, cm2);
			  final IValue v2 = this.eval(pred, c, s1, cm2);
			  if (v1.equals(v2)) {
				  return s1;
			  }
		  }
		  // Move on to the next action in the ActionItemList.
		  acts = acts.cdr();
		  pred = acts.carPred();
		  c = acts.carContext();
		  kind = acts.carKind();
          cm2 = acts.cm;
	  }
	  nss.addElement(s0, action, s1);
	  return s1.copy();
  }

  /* getNextStatesAppl */

  @ExpectInlined
  protected abstract TLCState getNextStatesAppl(final Action action, OpApplNode pred, ActionItemList acts, Context c,
          TLCState s0, TLCState s1, INextStateFunctor nss, final CostModel cm);
  
  protected final TLCState getNextStatesApplImpl(final Action action, final OpApplNode pred, final ActionItemList acts, final Context c,
                                           final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
        final ExprOrOpArgNode[] args = pred.getArgs();
        final int alen = args.length;
        final SymbolNode opNode = pred.getOperator();

        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        if (opcode == 0) {
          // This is a user-defined operator with one exception: it may
          // be substed by a builtin operator. This special case occurs
          // when the lookup returns an OpDef with opcode # 0.
          Object val = this.lookup(opNode, c, s0, false);

          if (val instanceof OpDefNode) {
				final OpDefNode opDef = (OpDefNode) val;
				opcode = BuiltInOPs.getOpCode(opDef.getName());
				if (opcode == 0) {
					return this.getNextStates(action, opDef.getBody(), acts, this.getOpContext(opDef, args, c, true, cm, toolId), s0, s1, nss, cm);
	            }
          }

          // Added by LL 13 Nov 2009 to fix Yuan's fix
          /*********************************************************************
           * Modified on 23 October 2012 by LL to work if ThmOrAssumpDefNode    *
           * imported with parameterized instantiation.                         *
           *********************************************************************/
          if (val instanceof ThmOrAssumpDefNode) {
            final ThmOrAssumpDefNode opDef = (ThmOrAssumpDefNode)val;
            return this.getNextStates(action, opDef.getBody(), acts, this.getOpContext(opDef, args, c, true), s0, s1, nss, cm);
          }

          if (val instanceof LazyValue) {
            final LazyValue lv = (LazyValue)val;
            if (lv.getValue() == null || lv.isUncachable()) {
              return this.getNextStates(action, lv.expr, acts, lv.con, s0, s1, nss, lv.cm);
            }
            val = lv.getValue();
          }

          //TODO If all eval/apply in getNextStatesApplEvalAppl would be side-effect free (ie. not mutate args, c, s0,...), 
          // this call could be moved into the if(opcode==0) branch below. However, opcode!=0 will only be the case if
          // OpDefNode above has been substed with a built-in operator. In other words, a user defines an operator Op1,
          // and re-defines Op1 with a TLA+ built-in one in a TLC model (not assumed to be common). => No point in trying
          // to move this call into if(opcode==0) because this will be the case most of the time anyway.
          final Object bval = getNextStatesApplEvalAppl(alen, args, c, s0, s1, cm, val);

	      // opcode == 0 is a user-defined operator.
          if (opcode == 0)
          {
            return getNextStatesApplUsrDefOp(action, pred, acts, s0, s1, nss, cm, bval);
          }
        }

        return getNextStatesApplSwitch(action, pred, acts, c, s0, s1, nss, cm, args, alen, opcode);
  }
  
  private final Object getNextStatesApplEvalAppl(final int alen, final ExprOrOpArgNode[] args, final Context c,
			final TLCState s0, final TLCState s1, final CostModel cm, final Object val) {
	      if (alen == 0) {
        if (val instanceof MethodValue) {
        	return ((MethodValue)val).apply(EmptyArgs, EvalControl.Clear);
        } else if (val instanceof EvaluatingValue) {
        	return ((EvaluatingValue)val).eval(this, args, c, s0, s1, EvalControl.Clear, cm);
       }
      }
      else {
        if (val instanceof OpValue) { // EvaluatingValue sub-class of OpValue!
       	  return ((OpValue) val).eval(this, args, c, s0, s1, EvalControl.Clear, cm);
        }
      }
      return val;
  }

  private final TLCState getNextStatesApplUsrDefOp(final Action action, final OpApplNode pred, final ActionItemList acts, final TLCState s0,
		final TLCState s1, final INextStateFunctor nss, final CostModel cm, final Object bval) {
	if (!(bval instanceof BoolValue))
	{
	  Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[] { "next states", "boolean",
	          bval.toString(), pred.toString() }, pred);
	}
	if (((BoolValue) bval).val)
	{
	  if (coverage) {
		  return this.getNextStates(action, acts, s0, s1, nss, cm);
	  } else {
		  return this.getNextStates0(action, acts, s0, s1, nss, cm);
	  }
	}
	return s1;
  }

  private final TLCState getNextStatesApplSwitch(final Action action, final OpApplNode pred, final ActionItemList acts, final Context c, final TLCState s0,
		final TLCState s1, final INextStateFunctor nss, final CostModel cm, final ExprOrOpArgNode[] args, final int alen, final int opcode) {
	TLCState resState = s1;
	switch (opcode) {
	case OPCODE_cl:     // ConjList
	case OPCODE_land:
	  {
	    ActionItemList acts1 = acts;
	    for (int i = alen - 1; i > 0; i--) {
	      acts1 = (ActionItemList) acts1.cons(args[i], c, cm, i);
	    }
	    return this.getNextStates(action, args[0], acts1, c, s0, s1, nss, cm);
	  }
	case OPCODE_dl:     // DisjList
	case OPCODE_lor:
	  {
		if (PROBABILISTIC) {
			// probabilistic (return after a state has been generated, ordered is randomized)
			final RandomGenerator rng = TLCGlobals.simulator.getRNG();
			int index = (int) Math.floor(rng.nextDouble() * alen);
			final int p = rng.nextPrime();
		    for (int i = 0; i < alen; i++) {
			      resState = this.getNextStates(action, args[index], acts, c, s0, resState, nss, cm);
				  if (nss.hasStates()) {
						return resState;
				  }
				  index = (index + p) % alen;
			}
		} else {
		    for (int i = 0; i < alen; i++) {
		      resState = this.getNextStates(action, args[i], acts, c, s0, resState, nss, cm);
		    }
		}
	    return resState;
	  }
	case OPCODE_be:     // BoundedExists
	  {
	    SemanticNode body = args[0];
	    
	    if (PROBABILISTIC) {
		    // probabilistic (return after a state has been generated, ordered is randomized)
			final ContextEnumerator Enum = this.contexts(Ordering.RANDOMIZED, pred, c, s0, s1, EvalControl.Clear, cm);
			Context c1;
		    while ((c1 = Enum.nextElement()) != null) {
				resState = this.getNextStates(action, body, acts, c1, s0, resState, nss, cm);
				if (nss.hasStates()) {
					return resState;
				}
		    }
	    } else {
	    	// non-deterministically generate successor states (potentially many)
	    	ContextEnumerator Enum = this.contexts(pred, c, s0, s1, EvalControl.Clear, cm);
	    	Context c1;
	    	while ((c1 = Enum.nextElement()) != null) {
	    		resState = this.getNextStates(action, body, acts, c1, s0, resState, nss, cm);
	    	}
	    }

	    return resState;
	  }
	case OPCODE_bf:     // BoundedForall
	  {
	    SemanticNode body = args[0];
	    ContextEnumerator Enum = this.contexts(pred, c, s0, s1, EvalControl.Clear, cm);
	    Context c1 = Enum.nextElement();
	    if (c1 == null) {
	      resState = this.getNextStates(action, acts, s0, s1, nss, cm);
	    }
	    else {
	      ActionItemList acts1 = acts;
	      Context c2;
	      while ((c2 = Enum.nextElement()) != null) {
	        acts1 = (ActionItemList) acts1.cons(body, c2, cm, IActionItemList.PRED);
	      }
	      resState = this.getNextStates(action, body, acts1, c1, s0, s1, nss, cm);
	    }
	    return resState;
	  }
	case OPCODE_fa:     // FcnApply
	  {
	    Value fval = this.eval(args[0], c, s0, s1, EvalControl.KeepLazy, cm);
	    if (fval instanceof FcnLambdaValue) {
	      FcnLambdaValue fcn = (FcnLambdaValue)fval;
	      if (fcn.fcnRcd == null) {
	        Context c1 = this.getFcnContext(fcn, args, c, s0, s1, EvalControl.Clear, cm);
	        return this.getNextStates(action, fcn.body, acts, c1, s0, s1, nss, fcn.cm);
	      }
	      fval = fcn.fcnRcd;
	    }
	    if (!(fval instanceof Applicable)) {
	      Assert.fail("In computing next states, a non-function (" +
	                  fval.getKindString() + ") was applied as a function.\n" + pred, pred, c);
	    }
	    Applicable fcn = (Applicable)fval;
	    Value argVal = this.eval(args[1], c, s0, s1, EvalControl.Clear, cm);
	    Value bval = fcn.apply(argVal, EvalControl.Clear);
	    if (!(bval instanceof BoolValue)) {
	      Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING2, new String[] { "next states", "boolean",
	              pred.toString() }, args[1], c);
	    }
	    if (((BoolValue)bval).val) {
	      return this.getNextStates(action, acts, s0, s1, nss, cm);
	    }
	    return resState;
	  }
	case OPCODE_aa:     // AngleAct <A>_e
	  {
	    ActionItemList acts1 = (ActionItemList) acts.cons(args[1], c, cm, IActionItemList.CHANGED);
	    return this.getNextStates(action, args[0], acts1, c, s0, s1, nss, cm);
	  }
	case OPCODE_sa:     // [A]_e
	  {
	    /* The following two lines of code did not work, and were changed by
	     * YuanYu to mimic the way \/ works.  Change made
	     *  11 Mar 2009, with LL sitting next to him.
	     */
	      //    this.getNextStates(action, args[0], acts, c, s0, s1, nss);
	      //    return this.processUnchanged(args[1], acts, c, s0, s1, nss);
	    resState = this.getNextStates(action, args[0], acts, c, s0, resState, nss, cm);
	    return this.processUnchanged(action, args[1], acts, c, s0, resState, nss, cm);
	  }
	case OPCODE_ite:    // IfThenElse
	  {
	    Value guard = this.eval(args[0], c, s0, s1, EvalControl.Clear, cm);
	    if (!(guard instanceof BoolValue)) {
	      Assert.fail("In computing next states, a non-boolean expression (" +
	                  guard.getKindString() + ") was used as the condition of" +
	                  " an IF." + pred, pred, c);
	    }
	    if (((BoolValue)guard).val) {
	      return this.getNextStates(action, args[1], acts, c, s0, s1, nss, cm);
	    }
	    else {
	      return this.getNextStates(action, args[2], acts, c, s0, s1, nss, cm);
	    }
	  }
	case OPCODE_case:   // Case
	  {
	    SemanticNode other = null;
		if (PROBABILISTIC) {
			// See Bounded exists above!
			throw new UnsupportedOperationException(
							"Probabilistic evaluation of next-state relation not implemented for CASE yet.");
		}
	    for (int i = 0; i < alen; i++) {
	      OpApplNode pair = (OpApplNode)args[i];
	      ExprOrOpArgNode[] pairArgs = pair.getArgs();
	      if (pairArgs[0] == null) {
	        other = pairArgs[1];
	      }
	      else {
	        Value bval = this.eval(pairArgs[0], c, s0, s1, EvalControl.Clear, coverage ? cm.get(args[i]) : cm);
	        if (!(bval instanceof BoolValue)) {
	          Assert.fail("In computing next states, a non-boolean expression (" +
	                      bval.getKindString() + ") was used as a guard condition" +
	                      " of a CASE.\n" + pairArgs[1], pairArgs[1], c);
	        }
	        if (((BoolValue)bval).val) {
	          return this.getNextStates(action, pairArgs[1], acts, c, s0, s1, nss, coverage ? cm.get(args[i]) : cm);
	        }
	      }
	    }
	    if (other == null) {
	      Assert.fail("In computing next states, TLC encountered a CASE with no" +
	                  " conditions true.\n" + pred, pred, c);
	    }
	    return this.getNextStates(action, other, acts, c, s0, s1, nss, coverage ? cm.get(args[alen - 1]) : cm);
	  }
	case OPCODE_eq:
	  {
	    SymbolNode var = this.getPrimedVar(args[0], c, false);
	    // Assert.check(var.getName().getVarLoc() >= 0);
	    if (var == null) {
	      Value bval = this.eval(pred, c, s0, s1, EvalControl.Clear, cm);
	      if (!((BoolValue)bval).val) {
	        return resState;
	      }
	    }
	    else {
	      UniqueString varName = var.getName();
	      IValue lval = s1.lookup(varName);
	      Value rval = this.eval(args[1], c, s0, s1, EvalControl.Clear, cm);
	      if (lval == null) {
	        resState.bind(varName, rval);
	        resState = this.getNextStates(action, acts, s0, resState, nss, cm);
	        resState.unbind(varName);
	        return resState;
	      }
	      else if (!lval.equals(rval)) {
	        return resState;
	      }
	    }
	    return this.getNextStates(action, acts, s0, s1, nss, cm);
	  }
	case OPCODE_in:
	  {
	    SymbolNode var = this.getPrimedVar(args[0], c, false);
	    // Assert.check(var.getName().getVarLoc() >= 0);
	    if (var == null) {
	      Value bval = this.eval(pred, c, s0, s1, EvalControl.Clear, cm);
	      if (!((BoolValue)bval).val) {
	        return resState;
	      }
	    }
	    else {
	      UniqueString varName = var.getName();
	      Value lval = (Value) s1.lookup(varName);
	      Value rval = this.eval(args[1], c, s0, s1, EvalControl.Clear, cm);
	      if (lval == null) {
	        if (!(rval instanceof Enumerable)) {
	          Assert.fail("In computing next states, the right side of \\IN" +
	                      " is not enumerable.\n" + pred, pred, c);
	        }
	        
			if (PROBABILISTIC) {
				final ValueEnumeration Enum = ((Enumerable)rval).elements(Ordering.RANDOMIZED);
				Value elem;
			    while ((elem = Enum.nextElement()) != null) {
			        resState.bind(varName, elem);
			        resState = this.getNextStates(action, acts, s0, resState, nss, cm);
			        resState.unbind(varName);
					if (nss.hasStates()) {
						return resState;
					}
			    }
			}

	        ValueEnumeration Enum = ((Enumerable)rval).elements();
	        Value elem;
	        while ((elem = Enum.nextElement()) != null) {
	          resState.bind(varName, elem);
	          resState = this.getNextStates(action, acts, s0, resState, nss, cm);
	          resState.unbind(varName);
	        }
	        return resState;
	      }
	      else if (!rval.member(lval)) {
	        return resState;
	      }
	    }
	    return this.getNextStates(action, acts, s0, s1, nss, cm);
	  }
	case OPCODE_implies:
	  {
	    Value bval = this.eval(args[0], c, s0, s1, EvalControl.Clear, cm);
	    if (!(bval instanceof BoolValue)) {
	      Assert.fail("In computing next states of a predicate of the form" +
	                  " P => Q, P was\n" + bval.getKindString() + ".\n" + pred, pred, c);
	    }
	    if (((BoolValue)bval).val) {
	      return this.getNextStates(action, args[1], acts, c, s0, s1, nss, cm);
	    }
	    else {
	      return this.getNextStates(action, acts, s0, s1, nss, cm);
	    }
	  }
	case OPCODE_unchanged:
	  {
	    return this.processUnchanged(action, args[0], acts, c, s0, s1, nss, cm);
	  }
	case OPCODE_cdot:
	  {
	    Assert.fail("The current version of TLC does not support action composition.", pred, c);
	    /***
	    TLCState s01 = TLCStateFun.Empty;
	    StateVec iss = new StateVec(0);
	    this.getNextStates(action, args[0], ActionItemList.Empty, c, s0, s01, iss);
	    int sz = iss.size();
	    for (int i = 0; i < sz; i++) {
	      s01 = iss.elementAt(i);
	      this.getNextStates(action, args[1], acts, c, s01, s1, nss);
	    }
	    ***/
	    return s1;
	  }
	// The following case added by LL on 13 Nov 2009 to handle subexpression names.
	case OPCODE_nop:
	{
	    return this.getNextStates(action, args[0], acts, c, s0, s1, nss, cm);
	}
	default:
	  {
	    // We handle all the other builtin operators here.
	    Value bval = this.eval(pred, c, s0, s1, EvalControl.Clear, cm);
	    if (!(bval instanceof BoolValue)) {
	      Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[] { "next states", "boolean",
	              bval.toString(), pred.toString() }, pred, c);
	    }
	    if (((BoolValue)bval).val) {
	      resState = this.getNextStates(action, acts, s0, s1, nss, cm);
	    }
	    return resState;
	  }
	}
  }
  
  /* processUnchanged */

  @ExpectInlined
  protected abstract TLCState processUnchanged(final Action action, SemanticNode expr, ActionItemList acts, Context c,
                                          TLCState s0, TLCState s1, INextStateFunctor nss, CostModel cm);
  
  protected final TLCState processUnchangedImpl(final Action action, SemanticNode expr, ActionItemList acts, Context c,
          TLCState s0, TLCState s1, INextStateFunctor nss, CostModel cm) {
    if (coverage){cm = cm.get(expr);}
        SymbolNode var = this.getVar(expr, c, false, toolId);
        TLCState resState = s1;
        if (var != null) {
            return processUnchangedImplVar(action, expr, acts, s0, s1, nss, var, cm);
        }

        if (expr instanceof OpApplNode) {
          OpApplNode expr1 = (OpApplNode)expr;
          ExprOrOpArgNode[] args = expr1.getArgs();
          int alen = args.length;
          SymbolNode opNode = expr1.getOperator();
          UniqueString opName = opNode.getName();
          int opcode = BuiltInOPs.getOpCode(opName);

          if (opcode == OPCODE_tup) {
            return processUnchangedImplTuple(action, acts, c, s0, s1, nss, args, alen, cm, coverage ? cm.get(expr1) : cm);
          }

          if (opcode == 0 && alen == 0) {
            // a 0-arity operator:
            return processUnchangedImpl0Arity(action, expr, acts, c, s0, s1, nss, cm, opNode, opName);
          }
        }

        return verifyUnchanged(action, expr, acts, c, s0, s1, nss, cm);
  }

  @ExpectInlined
  private final TLCState processUnchangedImpl0Arity(final Action action, final SemanticNode expr, final ActionItemList acts,
			final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm,
			final SymbolNode opNode, final UniqueString opName) {
		final Object val = this.lookup(opNode, c, false);
	
		if (val instanceof OpDefNode) {
		  return this.processUnchanged(action, ((OpDefNode)val).getBody(), acts, c, s0, s1, nss, cm);
		}
		else if (val instanceof LazyValue) {
		  final LazyValue lv = (LazyValue)val;
		  return this.processUnchanged(action, lv.expr, acts, lv.con, s0, s1, nss, cm);
		}
        return verifyUnchanged(action, expr, acts, c, s0, s1, nss, cm);
  }

  /**
   * Check that <code>expr</code> is unchanged without attempting to synthesize values for variables in the
   * successor state.
   */
  private TLCState verifyUnchanged(final Action action, final SemanticNode expr, final ActionItemList acts,
                                   final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss,
                                   final CostModel cm) {
      TLCState resState = s1;
      IValue v0 = this.eval(expr, c, s0, cm);
      IValue v1 = this.eval(expr, c, s1, TLCState.Null, EvalControl.Clear, cm);
      if (v0.equals(v1)) {
          resState = this.getNextStates(action, acts, s0, s1, nss, cm);
      }
      return resState;
  }

  @Override
  public IValue eval(SemanticNode expr, Context c, TLCState s0) {
	    return this.eval(expr, c, s0, TLCState.Empty, EvalControl.Clear, CostModel.DO_NOT_RECORD);
	  }

  @Override
  public IValue eval(SemanticNode expr, Context c) {
	    return this.eval(expr, c, TLCState.Empty);
	  }

  @Override
  public IValue eval(SemanticNode expr) {
	    return this.eval(expr, Context.Empty);
	  }

  @ExpectInlined
  private final TLCState processUnchangedImplTuple(final Action action, ActionItemList acts, Context c, TLCState s0, TLCState s1, INextStateFunctor nss,
  		ExprOrOpArgNode[] args, int alen, CostModel cm, CostModel cmNested) {
  	// a tuple:
  	if (alen != 0) {
  	  ActionItemList acts1 = acts;
  	  for (int i = alen-1; i > 0; i--) {
  	    acts1 = (ActionItemList) acts1.cons(args[i], c, cmNested, IActionItemList.UNCHANGED);
  	  }
  	  return this.processUnchanged(action, args[0], acts1, c, s0, s1, nss, cmNested);
  	}
  	return this.getNextStates(action, acts, s0, s1, nss, cm);
  }
  
  @ExpectInlined
  private final TLCState processUnchangedImplVar(final Action action, SemanticNode expr, ActionItemList acts, TLCState s0, TLCState s1, INextStateFunctor nss,
  		SymbolNode var, final CostModel cm) {
          TLCState resState = s1;
          // expr is a state variable:
          final UniqueString varName = var.getName();
          final IValue val0 = s0.lookup(varName);
          final IValue val1 = s1.lookup(varName);
          if (val1 == null) {
		  	resState.bind(varName, val0);
            if (coverage) {
            	resState = this.getNextStates(action, acts, s0, resState, nss, cm);
            } else {
            	resState = this.getNextStates0(action, acts, s0, resState, nss, cm);
            }
		  	resState.unbind(varName);
          }
          else if (val0.equals(val1)) {
              if (coverage) {
                  resState = this.getNextStates(action, acts, s0, s1, nss, cm);
              } else {
                  resState = this.getNextStates0(action, acts, s0, s1, nss, cm);
              }
          }
          else {
        	  MP.printWarning(EC.TLC_UNCHANGED_VARIABLE_CHANGED, new String[]{varName.toString(), expr.toString()});
          }
          return resState;
  }
    
  /* eval */
  public TLCState evalAlias(TLCState current, TLCState successor) {
		if ("".equals(this.config.getAlias())) {
			return current;
		}
		// see getState(..)
		IdThread.setCurrentState(current);
		
		// See asserts in tlc2.debug.TLCActionStackFrame.TLCActionStackFrame(TLCStackFrame, SemanticNode, Context, Tool, TLCState, Action, TLCState, RuntimeException)
		if (successor.getLevel() != current.getLevel()) {
			// Calling setPrecessor when the levels are equal would increase the level of
			// successor.
			successor.setPredecessor(current);
		}

		try {
			final TLCState alias = eval(getAliasSpec(), Context.Empty, current, successor, EvalControl.Clear).toState();
			if (alias != null) {
				return alias;
			}
		} catch (EvalException | TLCRuntimeException e) {
			// Fall back to original state if eval fails.
			return current;
		}
		
		return current;
  }

  	@Override
	public TLCStateInfo evalAlias(TLCStateInfo current, TLCState successor) {
		if (!hasAlias()) {
			return current;
		}
		return evalAlias(current, successor, Context.Empty);
	}

  	@Override
	public TLCStateInfo evalAlias(TLCStateInfo current, TLCState successor, Supplier<List<TLCStateInfo>> prefix) {
		if (!hasAlias()) {
			return current;
		}

		final ExternalModuleTable emt = getSpecProcessor().getSpecObj().getExternalModuleTable();
		final tla2sany.semantic.Context tlcExt = emt.getContext(UniqueString.of("TLCExt"));
		if (tlcExt == null) {
			// tlcExt is null if the TLCExt module is not extended or instantiated.  Thus,
			// Trace cannot appear in the spec.
			return evalAlias(current, successor, Context.Empty);
		}
		final SymbolNode tlcExtTrace = tlcExt.getSymbol(UniqueString.of("Trace"));
		
		return evalAlias(current, successor,
				Context.Empty.cons(tlcExtTrace, new LazySupplierValue(tlcExtTrace, (Supplier<Value>) () -> {
					return new TupleValue(
							prefix.get().stream().map(si -> new RecordValue(si.state)).toArray(Value[]::new));
				})));
	}

  private TLCStateInfo evalAlias(TLCStateInfo current, TLCState successor, Context ctxt) {

		// see getState(..)
		IdThread.setCurrentState(current.state);

		// See asserts in
		// tlc2.debug.TLCActionStackFrame.TLCActionStackFrame(TLCStackFrame,
		// SemanticNode, Context, Tool, TLCState, Action, TLCState, RuntimeException)
		if (successor.getLevel() != current.state.getLevel()) {
			// Calling setPrecessor when the levels are equal would increase the level of
			// successor.
			successor.setPredecessor(current);
		}

		try {
			final TLCState alias = eval(getAliasSpec(), ctxt, current.state, successor, EvalControl.Clear).toState();
			if (alias != null) {
				return new AliasTLCStateInfo(alias, current);
			}
		} catch (EvalException | TLCRuntimeException e) {
			// Fall back to original state if eval fails.
			return current;
			// TODO We have to somehow communicate this exception back to the user.
			// Unfortunately, the alias cannot be validated by SpecProcess (unless pure
			// constant expression who are too simple to be used in trace expressions).
			// Throwing the exception would be possible, but pretty annoying if TLC fails
			// to print an error trace because of a bogus alias after hours of model
			// checking (this is the very reason why the code falls back to return the 
			// original/current state).  Printing the exception to stdout/stderr here
			// would mess with the Toolbox's parsing that reads stdout back in.  It would
			// also look bad because we would print the error on every evaluation of the
			// alias and it's conceivable that -in most cases- evaluation would fail for
			// all evaluations.  This suggests that we have to defer reporting of evaluation
			// and runtime exception until after the error-trace has been printed. If
			// evaluation only failed for some invocations of evalAlias, the user will
			// be able to figure out the ones that failed by looking at the trace.  This
			// state should not be kept in Tool, because it doesn't know how to group
			// sequences of evalAlias invocations.
			// We could avoid keeping state entirely, if the exception was attached as an
			// "auxiliary" variable to the TLCStateInfo and printed as part of the error
			// trace.  The error trace would look strange, but it appears to be the best
			// compromise, especially if only some of the evaluations fail.
		}
		
		return current;
  }
  
  /* Special version of eval for state expressions. */
  @Override
  public IValue eval(SemanticNode expr, Context c, TLCState s0, CostModel cm) {
    return this.eval(expr, c, s0, TLCState.Empty, EvalControl.Clear, cm);
  }
  
	  @Override
	public final IValue eval(SemanticNode expr, Context c, TLCState s0,
              TLCState s1, final int control) {
		  return eval(expr, c, s0, s1, control, CostModel.DO_NOT_RECORD);
	  }
	  
	public Value evalPure(final OpDefNode opDef, final ExprOrOpArgNode[] args, final Context c, final TLCState s0,
				final TLCState s1, final int control, final CostModel cm) {
	    final Context c1 = this.getOpContext(opDef, args, c, true, cm, toolId);
		return this.eval(opDef.getBody(), c1, s0, s1, control, cm);
	}

  /*
   * This method evaluates the expression expr in the given context,
   * current state, and partial next state.
   */
  public abstract Value eval(SemanticNode expr, Context c, TLCState s0,
                          TLCState s1, final int control, final CostModel cm);
  
  @ExpectInlined
  protected Value evalImpl(final SemanticNode expr, final Context c, final TLCState s0,
          final TLCState s1, final int control, CostModel cm) {
        switch (expr.getKind()) {
        /***********************************************************************
        * LabelKind class added by LL on 13 Jun 2007.                          *
        ***********************************************************************/
        case LabelKind:
          {
            LabelNode expr1 = (LabelNode) expr;
            return this.eval(expr1.getBody(), c, s0, s1, control, cm);
          }
        case OpApplKind:
          {
            OpApplNode expr1 = (OpApplNode)expr;
            if (coverage) {cm = cm.get(expr);}
            return this.evalAppl(expr1, c, s0, s1, control, cm);
          }
        case LetInKind:
          {
            return evalImplLetInKind((LetInNode) expr, c, s0, s1, control, cm);
          }
        case SubstInKind:
          {
            return evalImplSubstInKind((SubstInNode) expr, c, s0, s1, control, cm);
          }
        // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
        case APSubstInKind:
          {
            return evalImplApSubstInKind((APSubstInNode) expr, c, s0, s1, control, cm);
          }
        case NumeralKind:
        case DecimalKind:
        case StringKind:
          {
            return (Value) WorkerValue.mux(expr.getToolObject(toolId));
          }
        case AtNodeKind:
          {
            return (Value)c.lookup(EXCEPT_AT);
          }
        case OpArgKind:
          {
            return evalImplOpArgKind((OpArgNode) expr, c, s0, s1, cm);
          }
        default:
          {
            Assert.fail("Attempted to evaluate an expression that cannot be evaluated.\n" +
                        expr, expr, c);
            return null;     // make compiler happy
          }
        }
  }

  @ExpectInlined
  private final Value evalImplLetInKind(LetInNode expr1, Context c, TLCState s0, TLCState s1, final int control, final CostModel cm) {
	OpDefNode[] letDefs = expr1.getLets();
	int letLen = letDefs.length;
	Context c1 = c;
	for (int i = 0; i < letLen; i++) {
	  OpDefNode opDef = letDefs[i];
	  if (opDef.getArity() == 0) {
	    Value rhs = new LazyValue(opDef.getBody(), c1, cm);
	    c1 = c1.cons(opDef, rhs);
	  }
	}
	return this.eval(expr1.getBody(), c1, s0, s1, control, cm);
  }

  @ExpectInlined
  private final Value evalImplSubstInKind(SubstInNode expr1, Context c, TLCState s0, TLCState s1, final int control, final CostModel cm) {
  	Subst[] subs = expr1.getSubsts();
  	int slen = subs.length;
  	Context c1 = c;
  	for (int i = 0; i < slen; i++) {
  	  Subst sub = subs[i];
  	  c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true, coverage ? sub.getCM() : cm, toolId));
  	}
  	return this.eval(expr1.getBody(), c1, s0, s1, control, cm);
  }
    
  @ExpectInlined
  private final Value evalImplApSubstInKind(APSubstInNode expr1, Context c, TLCState s0, TLCState s1, final int control, final CostModel cm) {
  	Subst[] subs = expr1.getSubsts();
  	int slen = subs.length;
  	Context c1 = c;
  	for (int i = 0; i < slen; i++) {
  	  Subst sub = subs[i];
  	  c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true, cm, toolId));
  	}
  	return this.eval(expr1.getBody(), c1, s0, s1, control, cm);
  }
  
  @ExpectInlined
  private final Value evalImplOpArgKind(OpArgNode expr1, Context c, TLCState s0, TLCState s1, final CostModel cm) {
  	SymbolNode opNode = expr1.getOp();
  	Object val = this.lookup(opNode, c, false);
  	if (val instanceof OpDefNode) {
  	  return setSource(expr1, new OpLambdaValue((OpDefNode)val, this, c, s0, s1, cm));
  	}
  	return (Value)val;
  }
  
  /* evalAppl */
  
  @ExpectInlined
  protected abstract Value evalAppl(final OpApplNode expr, Context c, TLCState s0,
          TLCState s1, final int control, final CostModel cm);

  protected final Value evalApplImpl(final OpApplNode expr, Context c, TLCState s0,
                              TLCState s1, final int control, CostModel cm) {
    if (coverage){
    	cm = cm.getAndIncrement(expr);
    }
        ExprOrOpArgNode[] args = expr.getArgs();
        SymbolNode opNode = expr.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        if (opcode == 0) {
          // This is a user-defined operator with one exception: it may
          // be substed by a builtin operator. This special case occurs
          // when the lookup returns an OpDef with opcode # 0.
          Object val = this.lookup(opNode, c, s0, EvalControl.isPrimed(control));

//          if (val instanceof Supplier) {
//        	  val = ((Supplier) val).get();
//          }
          
          // First, unlazy if it is a lazy value. We cannot use the cached
          // value when s1 == null or isEnabled(control).
			if (val instanceof LazyValue) {
				final LazyValue lv = (LazyValue) val;
				if (s1 == null) {
					val = this.eval(lv.expr, lv.con, s0, TLCState.Null, control, lv.getCostModel());
			    } else if (lv.isUncachable() || EvalControl.isEnabled(control)) {
					// Never use cached LazyValues in an ENABLED expression. This is why all
					// this.enabled* methods pass EvalControl.Enabled (the only exception being the
					// call on line line 2799 which passes EvalControl.Primed). This is why we can
			    	// be sure that ENALBED expressions are not affected by the caching bug tracked
			    	// in Github issue 113 (see below).
					val = this.eval(lv.expr, lv.con, s0, s1, control, lv.getCostModel());
				} else {
					val = lv.getValue();
					if (val == null) {
						final Value res = this.eval(lv.expr, lv.con, s0, s1, control, lv.getCostModel());
						// This check has been suggested by Yuan Yu on 01/15/2018:
						//
						// If init-states are being generated, level has to be <= ConstantLevel for
						// caching/LazyValue to be allowed. If next-states are being generated, level
						// has to be <= VariableLevel. The level indicates if the expression to be
						// evaluated contains only constants, constants & variables, constants & 
						// variables and primed variables (thus action) or is a temporal formula.
						//
						// This restriction is in place to fix Github issue 113
						// (https://github.com/tlaplus/tlaplus/issues/113) - 
						// TLC can generate invalid sets of init or next-states caused by broken
						// LazyValue evaluation. The related tests are AssignmentInit* and
						// AssignmentNext*. Without this fix TLC essentially reuses a stale lv.val when
						// it needs to re-evaluate res because the actual operands to eval changed.
						// Below is Leslie's formal description of the bug:
						// 
						// The possible initial values of some variable  var  are specified by a subformula
						// 
						// F(..., var, ...)
						// 
						// in the initial predicate, for some operator F such that expanding the
						// definition of F results in a formula containing more than one occurrence of
						// var , not all occurring in separate disjuncts of that formula.
						// 
						// The possible next values of some variable  var  are specified by a subformula
						// 
						// F(..., var', ...)
						// 
						// in the next-state relation, for some operator F such that expanding the
						// definition of F results in a formula containing more than one occurrence of
						// var' , not all occurring in separate disjuncts of that formula.
						// 
						// An example of the first case is an initial predicate  Init  defined as follows:
						// 
						// VARIABLES x, ...
						// F(var) == \/ var \in 0..99 /\ var % 2 = 0
						//           \/ var = -1
						// Init == /\ F(x)
						//         /\ ...
						// 
						// The error would not appear if  F  were defined by:
						// 
						// F(var) == \/ var \in {i \in 0..99 : i % 2 = 0}
						//           \/ var = -1
						// 
						// or if the definition of  F(x)  were expanded in  Init :
						// 
						// Init == /\ \/ x \in 0..99 /\ x % 2 = 0
						//            \/ x = -1
						//         /\ ...
						// 
						// A similar example holds for case 2 with the same operator F and the
						// next-state formula
						// 
						// Next == /\ F(x')
						//         /\ ...
						// 
						// The workaround is to rewrite the initial predicate or next-state relation so
						// it is not in the form that can cause the bug. The simplest way to do that is
						// to expand (in-line) the definition of F in the definition of the initial
						// predicate or next-state relation.
						//
						// Note that EvalControl.Init is only set in the scope of this.getInitStates*,
						// but not in the scope of methods such as this.isInModel, this.isGoodState...
						// which are invoked by DFIDChecker and ModelChecker#doInit and doNext. These
						// invocation however don't pose a problem with regards to issue 113 because
						// they don't generate the set of initial or next states but get passed fully
						// generated/final states.
						//
						// !EvalControl.isInit(control) means Tool is either processing the spec in
						// this.process* as part of initialization or that next-states are being
						// generated. The latter case has to restrict usage of cached LazyValue as
						// discussed above.
						final int level = ((LevelNode) lv.expr).getLevel(); // cast to LevelNode is safe because LV only subclass of SN.
						if ((EvalControl.isInit(control) && level <= LevelConstants.ConstantLevel)
								|| (!EvalControl.isInit(control) && level <= LevelConstants.VariableLevel)) {
							// The performance benefits of caching values is generally debatable. The time
							// it takes TLC to check a reasonable sized model of the PaxosCommit [1] spec is
							// ~2h with, with limited caching due to the fix for issue 113 or without
							// caching. There is no measurable performance difference even though the change
							// for issue 113 reduces the cache hits from ~13 billion to ~4 billion. This was
							// measured with an instrumented version of TLC.
							// [1] general/performance/PaxosCommit/  
							lv.setValue(res);
						}
						val = res;
					}
				}

			}

			Value res = null;
          if (val instanceof OpDefNode) {
            OpDefNode opDef = (OpDefNode)val;
            opcode = BuiltInOPs.getOpCode(opDef.getName());
            if (opcode == 0) {
              Context c1 = this.getOpContext(opDef, args, c, true, cm, toolId);
              res = this.eval(opDef.getBody(), c1, s0, s1, control, cm);
            }
          }
          else if (val instanceof Value) {
            res = (Value)val;
            int alen = args.length;
            if (alen == 0) {
              if (val instanceof MethodValue) {
                res = ((MethodValue)val).apply(EmptyArgs, EvalControl.Clear);
              } else if (val instanceof EvaluatingValue) {
            	  // Allow EvaluatingValue overwrites to have zero arity.
            	  res = ((EvaluatingValue) val).eval(this, args, c, s0, s1, control, cm);
              }
            }
            else {
              if (val instanceof OpValue) {
            	  res = ((OpValue) val).eval(this, args, c, s0, s1, control, cm);
               } 
            }
          }
          /*********************************************************************
          * The following added by Yuan Yu on 13 Nov 2009 to allow theorem an  *
          * assumption names to be used as expressions.                        *
          *                                                                    *
          * Modified on 23 October 2012 by LL to work if ThmOrAssumpDefNode    *
          * imported with parameterized instantiation.                         *
          *********************************************************************/
          else if (val instanceof ThmOrAssumpDefNode) {
//            Assert.fail("Trying to evaluate the theorem or assumption name `"
//                         + opNode.getName() + "'. \nUse `" + opNode.getName()
//                         + "!:' instead.\n" +expr);
            ThmOrAssumpDefNode opDef = (ThmOrAssumpDefNode) val ;
            Context c1 = this.getOpContext(opDef, args, c, true);
            return this.eval(opDef.getBody(), c1, s0, s1, control, cm);
          }
          else {
				if (!EvalControl.isEnabled(control) && EvalControl.isPrimed(control) && opNode instanceof OpDeclNode) {
					// We end up here if fairness is declared on a sub-action that doesn't define
					// the value of all variables given in the subscript vars (state pred) part of
					// the (weak or strong) fairness operator:
					// 
					// VARIABLES a,b            \* opNode is b up here.
					// vars == <<a,b>>
					// A == a' = 42
					// Next == A /\ b = b' \* Do something with b.
					// Spec == ... /\ WF_vars(A)
					//
					// Variants:
					//        /\ WF_b(TRUE)
					//        /\ WF_vars(TRUE)
					//
					// This variant is debatable. It triggers the "generic" exception below:
					//        /\ WF_vars(a' = b')
					//
					// For larger specs, this is obviously difficult to debug. Especially, 
					// because opNode usually points to b on the vars == <<...>> line.
					//
					// The following issues confirm that even seasoned users run into this:
					// https://github.com/tlaplus/tlaplus/issues/317
					// https://github.com/tlaplus/tlaplus/issues/618
					// http://discuss.tlapl.us/msg03840.html
					Assert.fail(EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_LIVE,
							new String[] { opNode.getName().toString(), expr.toString() }, expr, c);
					// Assert#fail throws exception, thus, no need for an else.
				}
				// EV#Enabled /\ EV#Prime /\ OpDeclNode is the case when A is an action (a boolean
				// valued transition function (see page 312 in Specifying Systems) appearing in an
				// invariant that TLC cannot evaluate. E.g.:
        	  	// 
	      	    // Spec == Init /\ [][a' = a + 1]_a
        	    // Inv == ENABLED a' > a
        	    // 
				// -----------
				// EV#Clear /\ OpDeclNode is the case when A is an action that TLC
				// cannot evaluate. E.g.:
	      	  	// 
	      	    // Spec == Init /\ [][a' > a]_a
	      	    // 
	            Assert.fail(EC.TLC_CONFIG_UNDEFINED_OR_NO_OPERATOR,
                new String[] { opNode.getName().toString(), expr.toString() }, expr, c);
          }
          if (opcode == 0) {
            return res;
          }
        }

        switch (opcode) {
        case OPCODE_bc:     // BoundedChoose
          {
            SemanticNode pred = args[0];
            SemanticNode inExpr = expr.getBdedQuantBounds()[0];
            Value inVal = this.eval(inExpr, c, s0, s1, control, cm);
            if (!(inVal instanceof Enumerable)) {
              Assert.fail("Attempted to compute the value of an expression of\n" +
                          "form CHOOSE x \\in S: P, but S was not enumerable.\n" + expr, expr, c);
            }

            // To fix Bugzilla Bug 279 : TLC bug caused by TLC's not preserving the semantics of CHOOSE
            // (@see tlc2.tool.BugzillaBug279Test),
            // the statement
            //
            //    inVal.normalize();
            //
            // was replaced by the following by LL on 7 Mar 2012.  This fix has not yet received
            // the blessing of Yuan Yu, so it should be considered to be provisional.
            // 
            //     Value convertedVal = inVal.ToSetEnum();
            //       if (convertedVal != null) {
            //         inVal = convertedVal;
            //       } else {
            //         inVal.normalize();
            //     }
            // end of fix.
            
            // MAK 09/22/2018:
			// The old fix above has the undesired side effect of enumerating inVal. In
			// other words, e.g. a SUBSET 1..8 would be enumerated and normalized into a
			// SetEnumValue. This is expensive and especially overkill, if the CHOOSE
			// predicate holds for most if not all elements of inVal. In this case, we
            // don't want to fully enumerate inVal but instead return the first element
			// obtained from Enumerable#elements for which the predicate holds. Thus,
			// Enumerable#elements(Ordering) has been added by which we make the requirement
			// for elements to be normalized explicit. Implementor of Enumerable, such as
			// SubsetValue are then free to implement elements that returns elements in
			// normalized order without converting SubsetValue into SetEnumValue first.
            
            inVal.normalize();

            ValueEnumeration enumSet = ((Enumerable)inVal).elements(Enumerable.Ordering.NORMALIZED);
            FormalParamNode[] bvars = expr.getBdedQuantSymbolLists()[0];
            boolean isTuple = expr.isBdedQuantATuple()[0];
            if (isTuple) {
              // Identifier tuple case:
              int cnt = bvars.length;
              Value val;
              while ((val = enumSet.nextElement()) != null) {
                TupleValue tv = (TupleValue) val.toTuple();
                if (tv == null || tv.size() != cnt) {
                  Assert.fail("Attempted to compute the value of an expression of form\n" +
                              "CHOOSE <<x1, ... , xN>> \\in S: P, but S was not a set\n" +
                              "of N-tuples.\n" + expr, expr, c);
                }
                Context c1 = c;
                for (int i = 0; i < cnt; i++) {
                  c1 = c1.cons(bvars[i], tv.elems[i]);
                }
                Value bval = this.eval(pred, c1, s0, s1, control, cm);
                if (!(bval instanceof BoolValue)) {
                  Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()}, pred, c1);
                }
                if (((BoolValue)bval).val) {
                  return (Value) val;
                }
              }
            }
            else {
              // Simple identifier case:
              SymbolNode name = bvars[0];
              Value val;
              while ((val = enumSet.nextElement()) != null) {
                Context c1 = c.cons(name, val);
                Value bval = this.eval(pred, c1, s0, s1, control, cm);
                if (!(bval instanceof BoolValue)) {
                  Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()}, pred, c1);
                }
                if (((BoolValue)bval).val) {
                  return (Value) val;
                }
              }
            }
            Assert.fail("Attempted to compute the value of an expression of form\n" +
                        "CHOOSE x \\in S: P, but no element of S satisfied P.\n" + expr, expr, c);
            return null;    // make compiler happy
          }
        case OPCODE_be:     // BoundedExists
          {
            ContextEnumerator Enum = this.contexts(expr, c, s0, s1, control, cm);
            SemanticNode body = args[0];
            Context c1;
            while ((c1 = Enum.nextElement()) != null) {
              Value bval = this.eval(body, c1, s0, s1, control, cm);
              if (!(bval instanceof BoolValue)) {
                Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()}, body, c1);
              }
              if (((BoolValue)bval).val) {
                return BoolValue.ValTrue;
              }
            }
            return BoolValue.ValFalse;
          }
        case OPCODE_bf:     // BoundedForall
          {
            ContextEnumerator Enum = this.contexts(expr, c, s0, s1, control, cm);
            SemanticNode body = args[0];
            Context c1;
            while ((c1 = Enum.nextElement()) != null) {
              Value bval = this.eval(body, c1, s0, s1, control, cm);
              if (!(bval instanceof BoolValue)) {
                Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()}, body, c1);
              }
              if (!((BoolValue)bval).val) {
                return BoolValue.ValFalse;
              }
            }
            return BoolValue.ValTrue;
          }
        case OPCODE_case:   // Case
          {
            int alen = args.length;
            SemanticNode other = null;
            for (int i = 0; i < alen; i++) {
              OpApplNode pairNode = (OpApplNode)args[i];
              ExprOrOpArgNode[] pairArgs = pairNode.getArgs();
              if (pairArgs[0] == null) {
                other = pairArgs[1];
                if (coverage) { cm = cm.get(pairNode); }
               }
              else {
                Value bval = this.eval(pairArgs[0], c, s0, s1, control, coverage ? cm.get(pairNode) : cm);
                if (!(bval instanceof BoolValue)) {
                  Assert.fail("A non-boolean expression (" + bval.getKindString() +
                              ") was used as a condition of a CASE. " + pairArgs[0], pairArgs[0], c);
                }
                if (((BoolValue)bval).val) {
                  return this.eval(pairArgs[1], c, s0, s1, control, coverage ? cm.get(pairNode) : cm);
                }
              }
            }
            if (other == null) {
              Assert.fail("Attempted to evaluate a CASE with no conditions true.\n" + expr, expr, c);
            }
            return this.eval(other, c, s0, s1, control, cm);
          }
        case OPCODE_cp:     // CartesianProd
          {
            int alen = args.length;
            Value[] sets = new Value[alen];
            for (int i = 0; i < alen; i++) {
              sets[i] = this.eval(args[i], c, s0, s1, control, cm);
            }
            return setSource(expr, new SetOfTuplesValue(sets, cm));
          }
        case OPCODE_cl:     // ConjList
          {
            int alen = args.length;
            for (int i = 0; i < alen; i++) {
              Value bval = this.eval(args[i], c, s0, s1, control, cm);
              if (!(bval instanceof BoolValue)) {
                Assert.fail("A non-boolean expression (" + bval.getKindString() +
                            ") was used as a formula in a conjunction.\n" + args[i], args[i], c);
              }
              if (!((BoolValue)bval).val) {
                return BoolValue.ValFalse;
              }
            }
            return BoolValue.ValTrue;
          }
        case OPCODE_dl:     // DisjList
          {
            int alen = args.length;
            for (int i = 0; i < alen; i++) {
              Value bval = this.eval(args[i], c, s0, s1, control, cm);
              if (!(bval instanceof BoolValue)) {
                Assert.fail("A non-boolean expression (" + bval.getKindString() +
                            ") was used as a formula in a disjunction.\n" + args[i], args[i], c);
              }
              if (((BoolValue)bval).val) {
                return BoolValue.ValTrue;
              }
            }
            return BoolValue.ValFalse;
          }
        case OPCODE_exc:    // Except
          {
            int alen = args.length;
            Value result = this.eval(args[0], c, s0, s1, control, cm);
            // SZ: variable not used ValueExcept[] expts = new ValueExcept[alen-1];
            for (int i = 1; i < alen; i++) {
              OpApplNode pairNode = (OpApplNode)args[i];
              ExprOrOpArgNode[] pairArgs = pairNode.getArgs();
              SemanticNode[] cmpts = ((OpApplNode)pairArgs[0]).getArgs();

              Value[] lhs = new Value[cmpts.length];
              for (int j = 0; j < lhs.length; j++) {
                lhs[j] = this.eval(cmpts[j], c, s0, s1, control,  coverage ? cm.get(pairNode).get(pairArgs[0]) : cm);
              }
              Value atVal = result.select(lhs);
              if (atVal == null) {
                // Do nothing but warn:
                  MP.printWarning(EC.TLC_EXCEPT_APPLIED_TO_UNKNOWN_FIELD, new String[]{args[0].toString()});
              }
              else {
                Context c1 = c.cons(EXCEPT_AT, atVal);
                Value rhs = this.eval(pairArgs[1], c1, s0, s1, control,  coverage ? cm.get(pairNode) : cm);
                ValueExcept vex = new ValueExcept(lhs, rhs);
                result = (Value) result.takeExcept(vex);
              }
            }
            return result;
          }
        case OPCODE_fa:     // FcnApply
          {
            Value result = null;
            Value fval = this.eval(args[0], c, s0, s1, EvalControl.setKeepLazy(control), cm);
            if ((fval instanceof FcnRcdValue) ||
                (fval instanceof FcnLambdaValue)) {
              Applicable fcn = (Applicable)fval;
              Value argVal = this.eval(args[1], c, s0, s1, control, cm);
              result = fcn.apply(argVal, control);
            }
            else if ((fval instanceof TupleValue) ||
                     (fval instanceof RecordValue)) {
              Applicable fcn = (Applicable)fval;
              if (args.length != 2) {
                Assert.fail("Attempted to evaluate an expression of form f[e1, ... , eN]" +
                            "\nwith f a tuple or record and N > 1.\n" + expr, expr, c);
              }
              Value aval = this.eval(args[1], c, s0, s1, control, cm);
              result = fcn.apply(aval, control);
            }
            else {
              Assert.fail("A non-function (" + fval.getKindString() + ") was applied" +
                          " as a function.\n" + expr, expr, c);
            }
            return result;
          }
        case OPCODE_fc:     // FcnConstructor
        case OPCODE_nrfs:   // NonRecursiveFcnSpec
        case OPCODE_rfs:    // RecursiveFcnSpec
          {
            FormalParamNode[][] formals = expr.getBdedQuantSymbolLists();
            boolean[] isTuples = expr.isBdedQuantATuple();
            ExprNode[] domains = expr.getBdedQuantBounds();

            Value[] dvals = new Value[domains.length];
            boolean isFcnRcd = true;
            for (int i = 0; i < dvals.length; i++) {
              dvals[i] = this.eval(domains[i], c, s0, s1, control, cm);
              isFcnRcd = isFcnRcd && (dvals[i] instanceof Reducible);
            }
            FcnParams params = new FcnParams(formals, isTuples, dvals);

            SemanticNode fbody = args[0];
            FcnLambdaValue fval = (FcnLambdaValue) setSource(expr, new FcnLambdaValue(params, fbody, this, c, s0, s1, control, cm));
            if (opcode == OPCODE_rfs) {
              SymbolNode fname = expr.getUnbdedQuantSymbols()[0];
              fval.makeRecursive(fname);
              isFcnRcd = false;
            }
            if (isFcnRcd && !EvalControl.isKeepLazy(control)) {
              return (Value) fval.toFcnRcd();
            }
            return fval;
          }
        case OPCODE_ite:    // IfThenElse
          {
            Value bval = this.eval(args[0], c, s0, s1, control, cm);
            if (!(bval instanceof BoolValue)) {
              Assert.fail("A non-boolean expression (" + bval.getKindString() +
                          ") was used as the condition of an IF.\n" + expr, expr, c);
            }
            if (((BoolValue)bval).val) {
              return this.eval(args[1], c, s0, s1, control, cm);
            }
            return this.eval(args[2], c, s0, s1, control, cm);
          }
        case OPCODE_rc:     // RcdConstructor
          {
            int alen = args.length;
            UniqueString[] names = new UniqueString[alen];
            Value[] vals = new Value[alen];
            for (int i = 0; i < alen; i++) {
              OpApplNode pairNode = (OpApplNode)args[i];
              ExprOrOpArgNode[] pair = pairNode.getArgs();
              names[i] = ((StringValue)pair[0].getToolObject(toolId)).getVal();
              vals[i] = this.eval(pair[1], c, s0, s1, control, coverage ? cm.get(pairNode) : cm);
            }
            return setSource(expr, new RecordValue(names, vals, false, cm));
          }
        case OPCODE_rs:     // RcdSelect
          {
            Value rval = this.eval(args[0], c, s0, s1, control, cm);
            Value sval = (Value) WorkerValue.mux(args[1].getToolObject(toolId));
            if (rval instanceof RecordValue) {
              Value result = (Value) ((RecordValue)rval).select(sval);
              if (result == null) {
                Assert.fail("Attempted to select nonexistent field " + sval + " from the" +
                            " record\n" + Values.ppr(rval.toString()) + "\n" + expr, expr, c);
              }
              return result;
            }
            else {
              FcnRcdValue fcn = (FcnRcdValue) rval.toFcnRcd();
              if (fcn == null) {
                Assert.fail("Attempted to select field " + sval + " from a non-record" +
                            " value " + Values.ppr(rval.toString()) + "\n" + expr, expr, c);
              }
              return fcn.apply(sval, control);
            }
          }
        case OPCODE_se:     // SetEnumerate
          {
            int alen = args.length;
            ValueVec vals = new ValueVec(alen);
            for (int i = 0; i < alen; i++) {
              vals.addElement(this.eval(args[i], c, s0, s1, control, cm));
            }
            return setSource(expr, new SetEnumValue(vals, false, cm));
          }
        case OPCODE_soa:    // SetOfAll: {e(x) : x \in S}
          {
            ValueVec vals = new ValueVec();
            ContextEnumerator Enum = this.contexts(expr, c, s0, s1, control, cm);
            SemanticNode body = args[0];
            Context c1;
            while ((c1 = Enum.nextElement()) != null) {
              Value val = this.eval(body, c1, s0, s1, control, cm);
              vals.addElement(val);
              // vals.addElement1(val);
            }
            return setSource(expr, new SetEnumValue(vals, false, cm));
          }
        case OPCODE_sor:    // SetOfRcds
          {
            int alen = args.length;
            UniqueString names[] = new UniqueString[alen];
            Value vals[] = new Value[alen];
            for (int i = 0; i < alen; i++) {
              OpApplNode pairNode = (OpApplNode)args[i];
              ExprOrOpArgNode[] pair = pairNode.getArgs();
              names[i] = ((StringValue)pair[0].getToolObject(toolId)).getVal();
              vals[i] = this.eval(pair[1], c, s0, s1, control, coverage ? cm.get(pairNode) : cm);
            }
            return setSource(expr, new SetOfRcdsValue(names, vals, false, cm));
          }
        case OPCODE_sof:    // SetOfFcns
          {
            Value lhs = this.eval(args[0], c, s0, s1, control, cm);
            Value rhs = this.eval(args[1], c, s0, s1, control, cm);
            return setSource(expr, new SetOfFcnsValue(lhs, rhs, cm));
          }
        case OPCODE_sso:    // SubsetOf
          {
            SemanticNode pred = args[0];
            SemanticNode inExpr = expr.getBdedQuantBounds()[0];
            Value inVal = this.eval(inExpr, c, s0, s1, control, cm);
            boolean isTuple = expr.isBdedQuantATuple()[0];
            FormalParamNode[] bvars = expr.getBdedQuantSymbolLists()[0];
            if (inVal instanceof Reducible) {
              ValueVec vals = new ValueVec();
              ValueEnumeration enumSet = ((Enumerable)inVal).elements();
              Value elem;
              if (isTuple) {
                while ((elem = enumSet.nextElement()) != null) {
                  Context c1 = c;
                  Value[] tuple = ((TupleValue)elem).elems;
                  for (int i = 0; i < bvars.length; i++) {
                    c1 = c1.cons(bvars[i], tuple[i]);
                  }
                  Value bval = this.eval(pred, c1, s0, s1, control, cm);
                  if (!(bval instanceof BoolValue)) {
                    Assert.fail("Attempted to evaluate an expression of form {x \\in S : P(x)}" +
                                " when P was " + bval.getKindString() + ".\n" + pred, pred, c1);
                  }
                  if (((BoolValue)bval).val) {
                    vals.addElement(elem);
                  }
                }
              }
              else {
                SymbolNode idName = bvars[0];
                while ((elem = enumSet.nextElement()) != null) {
                  Context c1 = c.cons(idName, elem);
                  Value bval = this.eval(pred, c1, s0, s1, control, cm);
                  if (!(bval instanceof BoolValue)) {
                    Assert.fail("Attempted to evaluate an expression of form {x \\in S : P(x)}" +
                                " when P was " + bval.getKindString() + ".\n" + pred, pred, c1);
                  }
                  if (((BoolValue)bval).val) {
                    vals.addElement(elem);
                  }
                }
              }
              return setSource(expr, new SetEnumValue(vals, inVal.isNormalized(), cm));
            }
            else if (isTuple) {
              return setSource(expr, new SetPredValue(bvars, inVal, pred, this, c, s0, s1, control, cm));
            }
            else {
              return setSource(expr, new SetPredValue(bvars[0], inVal, pred, this, c, s0, s1, control, cm));
            }
          }
        case OPCODE_tup:    // Tuple
          {
            int alen = args.length;
            Value[] vals = new Value[alen];
            for (int i = 0; i < alen; i++) {
              vals[i] = this.eval(args[i], c, s0, s1, control, cm);
            }
            return setSource(expr, new TupleValue(vals, cm));
          }
        case OPCODE_uc:     // UnboundedChoose
          {
            Assert.fail("TLC attempted to evaluate an unbounded CHOOSE.\n" +
                        "Make sure that the expression is of form CHOOSE x \\in S: P(x).\n" +
                        expr, expr, c);
            return null;    // make compiler happy
          }
        case OPCODE_ue:     // UnboundedExists
          {
            Assert.fail("TLC attempted to evaluate an unbounded \\E.\n" +
                        "Make sure that the expression is of form \\E x \\in S: P(x).\n" +
                        expr, expr, c);
            return null;    // make compiler happy
          }
        case OPCODE_uf:     // UnboundedForall
          {
            Assert.fail("TLC attempted to evaluate an unbounded \\A.\n" +
                        "Make sure that the expression is of form \\A x \\in S: P(x).\n" +
                        expr, expr, c);
            return null;    // make compiler happy
          }
        case OPCODE_lnot:
          {
            Value arg = this.eval(args[0], c, s0, s1, control, cm);
            if (!(arg instanceof BoolValue)) {
              Assert.fail("Attempted to apply the operator ~ to a non-boolean\n(" +
                          arg.getKindString() + ")\n" + expr, args[0], c);
            }
            return (((BoolValue)arg).val) ? BoolValue.ValFalse : BoolValue.ValTrue;
          }
        case OPCODE_subset:
          {
            Value arg = this.eval(args[0], c, s0, s1, control, cm);
			return setSource(expr, new SubsetValue(arg, cm));
          }
        case OPCODE_union:
          {
            Value arg = this.eval(args[0], c, s0, s1, control, cm);
            return setSource(expr, UnionValue.union(arg));
          }
        case OPCODE_domain:
          {
            Value arg = this.eval(args[0], c, s0, s1, control, cm);
            if (!(arg instanceof Applicable)) {
              Assert.fail("Attempted to apply the operator DOMAIN to a non-function\n(" +
                          arg.getKindString() + ")\n" + expr, expr, c);
            }
            return setSource(expr, ((Applicable)arg).getDomain());
          }
        case OPCODE_enabled:
          {
            TLCState sfun = TLCStateFun.Empty;
            Context c1 = Context.branch(c);
            sfun = this.enabled(args[0], ActionItemList.Empty, c1, s0, sfun, cm);
            return (sfun != null) ? BoolValue.ValTrue : BoolValue.ValFalse;
          }
        case OPCODE_eq:
          {
            Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
            Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
            return (arg1.equals(arg2)) ? BoolValue.ValTrue : BoolValue.ValFalse;
          }
        case OPCODE_land:
          {
            Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
            if (!(arg1 instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form P /\\ Q" +
                          " when P was\n" + arg1.getKindString() + ".\n" + expr, expr, c);
            }
            if (((BoolValue)arg1).val) {
              Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
              if (!(arg2 instanceof BoolValue)) {
                Assert.fail("Attempted to evaluate an expression of form P /\\ Q" +
                            " when Q was\n" + arg2.getKindString() + ".\n" + expr, expr, c);
              }
              return arg2;
            }
            return BoolValue.ValFalse;
          }
        case OPCODE_lor:
          {
            Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
            if (!(arg1 instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form P \\/ Q" +
                          " when P was\n" + arg1.getKindString() + ".\n" + expr, expr, c);
            }
            if (((BoolValue)arg1).val) {
              return BoolValue.ValTrue;
            }
            Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
            if (!(arg2 instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form P \\/ Q" +
                          " when Q was\n" + arg2.getKindString() + ".\n" + expr, expr, c);
            }
            return arg2;
          }
        case OPCODE_implies:
          {
            Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
            if (!(arg1 instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form P => Q" +
                          " when P was\n" + arg1.getKindString() + ".\n" + expr, expr, c);
            }
            if (((BoolValue)arg1).val) {
              Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
              if (!(arg2 instanceof BoolValue)) {
                Assert.fail("Attempted to evaluate an expression of form P => Q" +
                            " when Q was\n" + arg2.getKindString() + ".\n" + expr, expr, c);
              }
              return arg2;
            }
            return BoolValue.ValTrue;
          }
        case OPCODE_equiv:
          {
            Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
            Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
            if (!(arg1 instanceof BoolValue) || !(arg2 instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form P <=> Q" +
                          " when P or Q was not a boolean.\n" + expr, expr, c);
            }
            BoolValue bval1 = (BoolValue)arg1;
            BoolValue bval2 = (BoolValue)arg2;
            return (bval1.val == bval2.val) ? BoolValue.ValTrue : BoolValue.ValFalse;
          }
        case OPCODE_noteq:
          {
            Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
            Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
            return arg1.equals(arg2) ? BoolValue.ValFalse : BoolValue.ValTrue;
          }
        case OPCODE_subseteq:
          {
            Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
            Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
            if (!(arg1 instanceof Enumerable)) {
              Assert.fail("Attempted to evaluate an expression of form S \\subseteq T," +
                          " but S was not enumerable.\n" + expr, expr, c);
            }
            return ((Enumerable) arg1).isSubsetEq(arg2);
          }
        case OPCODE_in:
          {
            Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
            Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
            return (arg2.member(arg1)) ? BoolValue.ValTrue : BoolValue.ValFalse;
          }
        case OPCODE_notin:
          {
            Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
            Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
            return (arg2.member(arg1)) ? BoolValue.ValFalse : BoolValue.ValTrue;
          }
        case OPCODE_setdiff:
          {
            Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
            Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
            if (arg1 instanceof Reducible) {
              return setSource(expr, ((Reducible)arg1).diff(arg2));
            }
            return setSource(expr, new SetDiffValue(arg1, arg2));
          }
        case OPCODE_cap:
          {
            Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
            Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
            if (arg1 instanceof Reducible) {
              return setSource(expr, ((Reducible)arg1).cap(arg2));
            }
            else if (arg2 instanceof Reducible) {
              return setSource(expr, ((Reducible)arg2).cap(arg1));
            }
            return setSource(expr, new SetCapValue(arg1, arg2));
          }
        case OPCODE_nop:
          // Added by LL on 2 Aug 2007
          {
            return eval(args[0], c, s0, s1, control, cm);
          }
        case OPCODE_cup:
          {
            Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
            Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
            if (arg1 instanceof Reducible) {
              return setSource(expr, ((Reducible)arg1).cup(arg2));
            }
            else if (arg2 instanceof Reducible) {
              return setSource(expr, ((Reducible)arg2).cup(arg1));
            }
            return setSource(expr, new SetCupValue(arg1, arg2, cm));
          }
        case OPCODE_prime:
          {
        	  // MAK 03/2019:  Cannot reproduce this but without this check the nested evaluation
        	  // fails with a NullPointerException which subsequently is swallowed. This makes it 
        	  // impossible for a user to diagnose what is going on.  Since I cannot reproduce the
        	  // actual expression, I leave this commented for.  I recall an expression along the
        	  // lines of:
        	  //    ...
        	  //    TLCSet(23, CHOOSE p \in pc: pc[p] # pc[p]')
        	  //    ...
        	  // The fail statement below is obviously too generic to be useful and needs to be
        	  // clarified if the actual cause has been identified.
//        	  if (s1 == null) {
//                  Assert.fail("Attempted to evaluate the following expression," +
//                          " but expression failed to evaluate.\n" + expr);
//        	  }
            return this.eval(args[0], c, s1, TLCState.Null, EvalControl.setPrimedIfEnabled(control), cm);
          }
        case OPCODE_unchanged:
          {
            Value v0 = this.eval(args[0], c, s0, TLCState.Empty, control, cm);
            Value v1 = this.eval(args[0], c, s1, TLCState.Null, EvalControl.setPrimedIfEnabled(control), cm);
            return (v0.equals(v1)) ? BoolValue.ValTrue : BoolValue.ValFalse;
          }
        case OPCODE_aa:     // <A>_e
          {
            Value res = this.eval(args[0], c, s0, s1, control, cm);
            if (!(res instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form <A>_e," +
                          " but A was not a boolean.\n" + expr, expr, c);
            }
            if (!((BoolValue)res).val) {
              return BoolValue.ValFalse;
            }
            Value v0 = this.eval(args[1], c, s0, TLCState.Empty, control, cm);
            Value v1 = this.eval(args[1], c, s1, TLCState.Null, EvalControl.setPrimedIfEnabled(control), cm);
            return v0.equals(v1) ? BoolValue.ValFalse : BoolValue.ValTrue;
          }
        case OPCODE_sa:     // [A]_e
          {
            Value res = this.eval(args[0], c, s0, s1, control, cm);
            if (!(res instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form [A]_e," +
                          " but A was not a boolean.\n" + expr, expr, c);
            }
            if (((BoolValue)res).val) {
              return BoolValue.ValTrue;
            }
            Value v0 = this.eval(args[1], c, s0, TLCState.Empty, control, cm);
            Value v1 = this.eval(args[1], c, s1, TLCState.Null, EvalControl.setPrimedIfEnabled(control), cm);
            return (v0.equals(v1)) ? BoolValue.ValTrue : BoolValue.ValFalse;
          }
        case OPCODE_cdot:
          {
            Assert.fail("The current version of TLC does not support action composition.", expr, c);
            /***
            TLCState s01 = TLCStateFun.Empty;
            StateVec iss = new StateVec(0);
            this.getNextStates(args[0], ActionItemList.Empty, c, s0, s01, iss);
            int sz = iss.size();
            for (int i = 0; i < sz; i++) {
              s01 = iss.elementAt(i);
              this.eval(args[1], c, s01, s1, control);
            }
            ***/
            return null;    // make compiler happy
          }
        case OPCODE_sf:     // SF
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"SF", expr.toString()}, expr, c);
            return null;    // make compiler happy
          }
        case OPCODE_wf:     // WF
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"WF", expr.toString()}, expr, c);
            return null;    // make compiler happy
          }
        case OPCODE_te:     // TemporalExists
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"\\EE", expr.toString()}, expr, c);
            return null;    // make compiler happy
          }
        case OPCODE_tf:     // TemporalForAll
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"\\AA", expr.toString()}, expr, c);
            return null;    // make compiler happy
          }
        case OPCODE_leadto:
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"a ~> b", expr.toString()}, expr, c);
            return null;    // make compiler happy
          }
        case OPCODE_arrow:
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"a -+-> formula", expr.toString()}, expr, c);
            return null;    // make compiler happy
          }
        case OPCODE_box:
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"[]A", expr.toString()}, expr, c);
            return null;    // make compiler happy
          }
        case OPCODE_diamond:
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"<>A", expr.toString()}, expr, c);
            return null;    // make compiler happy
          }

        default:
          {
            Assert.fail("TLC BUG: could not evaluate this expression.\n" + expr, expr, c);
            return null;
          }
        }
  }

  protected abstract Value setSource(final SemanticNode expr, final Value value);

  /**
   * This method determines if the argument is a valid state.  A state
   * is good iff it assigns legal explicit values to all the global
   * state variables.
   */
  @Override
  public final boolean isGoodState(TLCState state) {
    return state.allAssigned();
  }

  /* This method determines if a state satisfies the model constraints. */
  @Override
  public final boolean isInModel(TLCState state) throws EvalException {
    ExprNode[] constrs = this.getModelConstraints();
    for (int i = 0; i < constrs.length; i++) {
      final CostModel cm = coverage ? ((Action) constrs[i].getToolObject(toolId)).cm : CostModel.DO_NOT_RECORD;
      IValue bval = this.eval(constrs[i], Context.Empty, state, cm);
      if (!(bval instanceof BoolValue)) {
        Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", constrs[i].toString()}, constrs[i]);
      }
      if (!((BoolValue)bval).val) {
  		  if (coverage) {
  			  cm.incInvocations();
		  }
    	  return false;
      } else {
  		  if (coverage) {
  			  cm.incSecondary();
		  }
      }
    }
    return true;
  }

  /* This method determines if a pair of states satisfy the action constraints. */
  @Override
  public final boolean isInActions(TLCState s1, TLCState s2) throws EvalException {
    ExprNode[] constrs = this.getActionConstraints();
    for (int i = 0; i < constrs.length; i++) {
      final CostModel cm = coverage ? ((Action) constrs[i].getToolObject(toolId)).cm : CostModel.DO_NOT_RECORD;
      Value bval = this.eval(constrs[i], Context.Empty, s1, s2, EvalControl.Clear, cm);
      if (!(bval instanceof BoolValue)) {
        Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", constrs[i].toString()}, constrs[i]);
      }
      if (!((BoolValue)bval).val) {
  		  if (coverage) {
			  cm.incInvocations();
		  }
    	  return false;
      } else {
  		  if (coverage) {
  			  cm.incSecondary();
		  }
      }
    }
    return true;
  }
  
  @Override
  public final boolean hasStateOrActionConstraints() {
	  return this.getModelConstraints().length > 0 || this.getActionConstraints().length > 0;
  }
  
  @Override
  public final TLCState enabled(SemanticNode pred, Context c, TLCState s0, TLCState s1) {
		  return enabled(pred, ActionItemList.Empty, c, s0, s1, CostModel.DO_NOT_RECORD);
  }
  
  @Override
  public final TLCState enabled(SemanticNode pred, Context c, TLCState s0, TLCState s1, ExprNode subscript, final int ail) {
      ActionItemList acts = (ActionItemList) ActionItemList.Empty.cons(subscript, c, CostModel.DO_NOT_RECORD, ail);
	  return enabled(pred, acts, c, s0, s1, CostModel.DO_NOT_RECORD);
  }
  
  @Override
  public final TLCState enabled(SemanticNode pred, IActionItemList acts, Context c, TLCState s0, TLCState s1) {
		  return enabled(pred, acts, c, s0, s1, CostModel.DO_NOT_RECORD);
  }

  /**
   * This method determines if an action is enabled in the given state.
   * More precisely, it determines if (act.pred /\ (sub' # sub)) is
   * enabled in the state s and context act.con.
   */
  @Override
  public abstract TLCState enabled(SemanticNode pred, IActionItemList acts,
                                Context c, TLCState s0, TLCState s1, CostModel cm);

  protected final TLCState enabledImpl(SemanticNode pred, ActionItemList acts,
          Context c, TLCState s0, TLCState s1, CostModel cm) {
        switch (pred.getKind()) {
        case OpApplKind:
          {
            OpApplNode pred1 = (OpApplNode)pred;
            return this.enabledAppl(pred1, acts, c, s0, s1, cm);
          }
        case LetInKind:
          {
            LetInNode pred1 = (LetInNode)pred;
            OpDefNode[] letDefs = pred1.getLets();
            Context c1 = c;
            for (int i = 0; i < letDefs.length; i++) {
              OpDefNode opDef = letDefs[i];
              if (opDef.getArity() == 0) {
                Value rhs = new LazyValue(opDef.getBody(), c1, cm);
                c1 = c1.cons(opDef, rhs);
              }
            }
            return this.enabled(pred1.getBody(), acts, c1, s0, s1, cm);
          }
        case SubstInKind:
          {
            SubstInNode pred1 = (SubstInNode)pred;
            Subst[] subs = pred1.getSubsts();
            int slen = subs.length;
            Context c1 = c;
            for (int i = 0; i < slen; i++) {
              Subst sub = subs[i];
              c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, coverage ? sub.getCM() : cm, toolId));
            }
            return this.enabled(pred1.getBody(), acts, c1, s0, s1, cm);
          }
        // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
        case APSubstInKind:
          {
            APSubstInNode pred1 = (APSubstInNode)pred;
            Subst[] subs = pred1.getSubsts();
            int slen = subs.length;
            Context c1 = c;
            for (int i = 0; i < slen; i++) {
              Subst sub = subs[i];
              c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, cm, toolId));
            }
            return this.enabled(pred1.getBody(), acts, c1, s0, s1, cm);
          }
        // LabelKind class added by LL on 13 Jun 2007
        case LabelKind:
          {
            LabelNode pred1 = (LabelNode)pred;
            return this.enabled(pred1.getBody(), acts, c, s0, s1, cm);
          }
        default:
          {
            // We should not compute enabled on anything else.
            Assert.fail("Attempted to compute ENABLED on a non-boolean expression.\n" + pred, pred, c);
            return null;    // make compiler happy
          }
        }
  }

  private final TLCState enabled(ActionItemList acts, TLCState s0, TLCState s1, CostModel cm) {
    if (acts.isEmpty()) return s1;

    final int kind = acts.carKind();
    SemanticNode pred = acts.carPred();
    Context c = acts.carContext();
    cm = acts.cm;
    ActionItemList acts1 = acts.cdr();
    if (kind > IActionItemList.CONJUNCT) {
      TLCState res = this.enabled(pred, acts1, c, s0, s1, cm);
      return res;
    }
    else if (kind == IActionItemList.PRED) {
      TLCState res = this.enabled(pred, acts1, c, s0, s1, cm);
      return res;
    }
    if (kind == IActionItemList.UNCHANGED) {
      TLCState res = this.enabledUnchanged(pred, acts1, c, s0, s1, cm);
      return res;
    }

    Value v1 = this.eval(pred, c, s0, TLCState.Empty, EvalControl.Enabled, cm);
	// We are now in ENABLED and primed state. Second TLCState parameter being null
	// effectively disables LazyValue in evalAppl (same effect as
	// EvalControl.setPrimed(EvalControl.Enabled)).
    Value v2 = this.eval(pred, c, s1, TLCState.Null, EvalControl.Primed, cm);

    if (v1.equals(v2)) return null;
    TLCState res = this.enabled(acts1, s0, s1, cm);
    return res;
  }

  protected abstract TLCState enabledAppl(OpApplNode pred, ActionItemList acts, Context c, TLCState s0, TLCState s1, CostModel cm);

  protected final TLCState enabledApplImpl(OpApplNode pred, ActionItemList acts, Context c, TLCState s0, TLCState s1, CostModel cm)
  {
    if (coverage) {cm = cm.get(pred);}
        ExprOrOpArgNode[] args = pred.getArgs();
        int alen = args.length;
        SymbolNode opNode = pred.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        if (opcode == 0)
        {
          // This is a user-defined operator with one exception: it may
          // be substed by a builtin operator. This special case occurs
          // when the lookup returns an OpDef with opcode # 0.
          Object val = this.lookup(opNode, c, s0, false);

          if (val instanceof OpDefNode)
          {
            OpDefNode opDef = (OpDefNode) val;
            opcode = BuiltInOPs.getOpCode(opDef.getName());
            if (opcode == 0)
            {
              // Context c1 = this.getOpContext(opDef, args, c, false);
              Context c1 = this.getOpContext(opDef, args, c, true, cm, toolId);
              return this.enabled(opDef.getBody(), acts, c1, s0, s1, cm);
            }
          }


          // Added 13 Nov 2009 by LL to handle theorem or assumption names
          /*********************************************************************
          * Modified on 23 October 2012 by LL to work if ThmOrAssumpDefNode    *
          * imported with parameterized instantiation.                         *
          *********************************************************************/
          if (val instanceof ThmOrAssumpDefNode)
          {
            ThmOrAssumpDefNode opDef = (ThmOrAssumpDefNode) val;
            Context c1 = this.getOpContext(opDef, args, c, true);
            return this.enabled(opDef.getBody(), acts, c1, s0, s1, cm);
          }


          if (val instanceof LazyValue)
          {
            LazyValue lv = (LazyValue) val;
            return this.enabled(lv.expr, acts, lv.con, s0, s1, lv.cm);
          }

          Object bval = val;
          if (alen == 0)
          {
            if (val instanceof MethodValue)
            {
              bval = ((MethodValue) val).apply(EmptyArgs, EvalControl.Clear); // EvalControl.Clear is ignored by MethodValuea#apply
            } else if (val instanceof EvaluatingValue) {
              bval = ((EvaluatingValue) val).eval(this, args, c, s0, s1, EvalControl.Enabled, cm);
            }
          } else
          {
            if (val instanceof OpValue)
            {
            	bval = ((OpValue) val).eval(this, args, c, s0, s1, EvalControl.Enabled, cm);
             }
          }

          if (opcode == 0)
          {
            if (!(bval instanceof BoolValue))
            {
              Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[] { "ENABLED", "boolean",
                      bval.toString(), pred.toString() }, pred, c);
            }
            if (((BoolValue) bval).val)
            {
              return this.enabled(acts, s0, s1, cm);
            }
            return null;
          }
        }

        switch (opcode) {
        case OPCODE_aa: // AngleAct <A>_e
          {
        	  ActionItemList acts1 = (ActionItemList) acts.cons(args[1], c, cm, IActionItemList.CHANGED);
            return this.enabled(args[0], acts1, c, s0, s1, cm);
          }
        case OPCODE_be: // BoundedExists
          {
            SemanticNode body = args[0];
            ContextEnumerator Enum = this.contexts(pred, c, s0, s1, EvalControl.Enabled, cm);
            Context c1;
            while ((c1 = Enum.nextElement()) != null)
            {
              TLCState s2 = this.enabled(body, acts, c1, s0, s1, cm);
              if (s2 != null) {
                return s2;
              }
            }
            return null;
          }
        case OPCODE_bf: // BoundedForall
          {
            SemanticNode body = args[0];
            ContextEnumerator Enum = this.contexts(pred, c, s0, s1, EvalControl.Enabled, cm);
            Context c1 = Enum.nextElement();
            if (c1 == null)
            {
              return this.enabled(acts, s0, s1, cm);
            }
            ActionItemList acts1 = acts;
            Context c2;
            while ((c2 = Enum.nextElement()) != null)
            {
              acts1 = (ActionItemList) acts1.cons(body, c2, cm, IActionItemList.PRED);
            }
            return this.enabled(body, acts1, c1, s0, s1, cm);
          }
        case OPCODE_case: // Case
          {
            SemanticNode other = null;
            for (int i = 0; i < alen; i++)
            {
              OpApplNode pair = (OpApplNode) args[i];
              ExprOrOpArgNode[] pairArgs = pair.getArgs();
              if (pairArgs[0] == null)
              {
                other = pairArgs[1];
              } else
              {
                Value bval = this.eval(pairArgs[0], c, s0, s1, EvalControl.Enabled, cm);
                if (!(bval instanceof BoolValue))
                {
                  Assert.fail("In computing ENABLED, a non-boolean expression(" + bval.getKindString()
                          + ") was used as a guard condition" + " of a CASE.\n" + pairArgs[1], pairArgs[1], c);
                }
                if (((BoolValue) bval).val)
                {
                  return this.enabled(pairArgs[1], acts, c, s0, s1, cm);
                }
              }
            }
            if (other == null)
            {
              Assert.fail("In computing ENABLED, TLC encountered a CASE with no" + " conditions true.\n" + pred, pred, c);
            }
            return this.enabled(other, acts, c, s0, s1, cm);
          }
        case OPCODE_cl: // ConjList
        case OPCODE_land:
          {
            ActionItemList acts1 = acts;
            for (int i = alen - 1; i > 0; i--)
            {
              acts1 = (ActionItemList) acts1.cons(args[i], c, cm, i);
            }
            return this.enabled(args[0], acts1, c, s0, s1, cm);
          }
        case OPCODE_dl: // DisjList
        case OPCODE_lor:
          {
            for (int i = 0; i < alen; i++)
            {
              TLCState s2 = this.enabled(args[i], acts, c, s0, s1, cm);
              if (s2 != null) {
                return s2;
              }
            }
            return null;
          }
        case OPCODE_fa: // FcnApply
          {
            Value fval = this.eval(args[0], c, s0, s1, EvalControl.setKeepLazy(EvalControl.Enabled), cm); // KeepLazy does not interfere with EvalControl.Enabled in this.evalAppl
            if (fval instanceof FcnLambdaValue)
            {
              FcnLambdaValue fcn = (FcnLambdaValue) fval;
              if (fcn.fcnRcd == null)
              {
                Context c1 = this.getFcnContext(fcn, args, c, s0, s1, EvalControl.Enabled, cm); // EvalControl.Enabled passed on to nested this.evalAppl
                return this.enabled(fcn.body, acts, c1, s0, s1, cm);
              }
              fval = fcn.fcnRcd;
            }
            if (fval instanceof Applicable)
            {
              Applicable fcn = (Applicable) fval;
              Value argVal = this.eval(args[1], c, s0, s1, EvalControl.Enabled, cm);
              Value bval = fcn.apply(argVal, EvalControl.Enabled); // EvalControl.Enabled not taken into account by any subclass of Applicable
              if (!(bval instanceof BoolValue))
              {
                Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING2, new String[] { "ENABLED", "boolean",
                        pred.toString() }, args[1], c);
              }
              if (!((BoolValue) bval).val) {
                return null;
              }
            } else
            {
              Assert.fail("In computing ENABLED, a non-function (" + fval.getKindString()
                      + ") was applied as a function.\n" + pred, pred, c);
            }
            return this.enabled(acts, s0, s1, cm);
          }
        case OPCODE_ite: // IfThenElse
          {
            Value guard = this.eval(args[0], c, s0, s1, EvalControl.Enabled, cm);
            if (!(guard instanceof BoolValue))
            {
              Assert.fail("In computing ENABLED, a non-boolean expression(" + guard.getKindString()
                      + ") was used as the guard condition" + " of an IF.\n" + pred, pred, c);
            }
            int idx = (((BoolValue) guard).val) ? 1 : 2;
            return this.enabled(args[idx], acts, c, s0, s1, cm);
          }
        case OPCODE_sa: // SquareAct [A]_e
          {
            TLCState s2 = this.enabled(args[0], acts, c, s0, s1, cm);
            if (s2 != null) {
              return s2;
            }
            return this.enabledUnchanged(args[1], acts, c, s0, s1, cm);
          }
        case OPCODE_te: // TemporalExists
        case OPCODE_tf: // TemporalForAll
          {
            Assert.fail("In computing ENABLED, TLC encountered temporal quantifier.\n" + pred, pred, c);
            return null; // make compiler happy
          }
        case OPCODE_uc: // UnboundedChoose
          {
            Assert.fail("In computing ENABLED, TLC encountered unbounded CHOOSE. "
                    + "Make sure that the expression is of form CHOOSE x \\in S: P(x).\n" + pred, pred, c);
            return null; // make compiler happy
          }
        case OPCODE_ue: // UnboundedExists
          {
            Assert.fail("In computing ENABLED, TLC encountered unbounded quantifier. "
                    + "Make sure that the expression is of form \\E x \\in S: P(x).\n" + pred, pred, c);
            return null; // make compiler happy
          }
        case OPCODE_uf: // UnboundedForall
          {
            Assert.fail("In computing ENABLED, TLC encountered unbounded quantifier. "
                    + "Make sure that the expression is of form \\A x \\in S: P(x).\n" + pred, pred, c);
            return null; // make compiler happy
          }
        case OPCODE_sf: // SF
          {
            Assert.fail(EC.TLC_ENABLED_WRONG_FORMULA, new String[]{ "SF", pred.toString()}, pred, c);
            return null; // make compiler happy
          }
        case OPCODE_wf: // WF
          {
            Assert.fail(EC.TLC_ENABLED_WRONG_FORMULA, new String[] { "WF", pred.toString() }, pred, c);
            return null; // make compiler happy
          }
        case OPCODE_box:
          {
            Assert.fail(EC.TLC_ENABLED_WRONG_FORMULA, new String[] { "[]", pred.toString() }, pred, c);
            return null; // make compiler happy
          }
        case OPCODE_diamond:
          {
            Assert.fail(EC.TLC_ENABLED_WRONG_FORMULA, new String[] { "<>", pred.toString() }, pred, c);
            return null; // make compiler happy
          }
        case OPCODE_unchanged:
          {
            return this.enabledUnchanged(args[0], acts, c, s0, s1, cm);
          }
        case OPCODE_eq:
          {
            SymbolNode var = this.getPrimedVar(args[0], c, true);
            if (var == null)
            {
              Value bval = this.eval(pred, c, s0, s1, EvalControl.Enabled, cm);
              if (!((BoolValue) bval).val) {
                return null;
              }
            } else
            {
              UniqueString varName = var.getName();
              IValue lval = s1.lookup(varName);
              Value rval = this.eval(args[1], c, s0, s1, EvalControl.Enabled, cm);
              if (lval == null)
              {
                TLCState s2 = s1.bind(var, rval);
                return this.enabled(acts, s0, s2, cm);
              } else
              {
                if (!lval.equals(rval)) {
                  return null;
                }
              }
            }
            return this.enabled(acts, s0, s1, cm);
          }
        case OPCODE_implies:
          {
            Value bval = this.eval(args[0], c, s0, s1, EvalControl.Enabled, cm);
            if (!(bval instanceof BoolValue))
            {
              Assert.fail("While computing ENABLED of an expression of the form" + " P => Q, P was "
                      + bval.getKindString() + ".\n" + pred, pred, c);
            }
            if (((BoolValue) bval).val)
            {
              return this.enabled(args[1], acts, c, s0, s1, cm);
            }
            return this.enabled(acts, s0, s1, cm);
          }
        case OPCODE_cdot:
          {
            Assert.fail("The current version of TLC does not support action composition.", pred, c);
            /***
            TLCState s01 = TLCStateFun.Empty;
            StateVec iss = new StateVec(0);
            this.getNextStates(args[0], ActionItemList.Empty, c, s0, s01, iss);
            int sz = iss.size();
            for (int i = 0; i < sz; i++) {
              s01 = iss.elementAt(i);
              TLCState s2 = this.enabled(args[1], acts, c, s01, s1);
              if (s2 != null) return s2;
            }
            ***/
            return null; // make compiler happy
          }
        case OPCODE_leadto:
          {
            Assert.fail("In computing ENABLED, TLC encountered a temporal formula" + " (a ~> b).\n" + pred, pred, c);
            return null; // make compiler happy
          }
        case OPCODE_arrow:
          {
            Assert.fail("In computing ENABLED, TLC encountered a temporal formula" + " (a -+-> formula).\n" + pred, pred, c);
            return null; // make compiler happy
          }
        case OPCODE_in:
          {
            SymbolNode var = this.getPrimedVar(args[0], c, true);
            if (var == null)
            {
                Value bval = this.eval(pred, c, s0, s1, EvalControl.Enabled, cm);
                if (!((BoolValue) bval).val) {
                  return null;
                }
            } else
            {
              UniqueString varName = var.getName();
              Value lval = (Value) s1.lookup(varName);
              Value rval = this.eval(args[1], c, s0, s1, EvalControl.Enabled, cm);
              if (lval == null)
              {
                if (!(rval instanceof Enumerable))
                {
                  Assert.fail("The right side of \\IN is not enumerable.\n" + pred, pred, c);
                }
                ValueEnumeration Enum = ((Enumerable) rval).elements();
                Value val;
                while ((val = Enum.nextElement()) != null)
                {
                  TLCState s2 = s1.bind(var, val);
                  s2 = this.enabled(acts, s0, s2, cm);
                  if (s2 != null) {
                    return s2;
                  }
                }
                return null;
              } else
              {
                if (!rval.member(lval)) {
                  return null;
                }
              }
            }
            return this.enabled(acts, s0, s1, cm);
          }
        // The following case added by LL on 13 Nov 2009 to handle subexpression names.
        case OPCODE_nop:
          {
            return this.enabled(args[0], acts, c, s0, s1, cm);
          }

        default:
          {
            // We handle all the other builtin operators here.
            Value bval = this.eval(pred, c, s0, s1, EvalControl.Enabled, cm);
            if (!(bval instanceof BoolValue))
            {
              Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[] { "ENABLED", "boolean",
                      bval.toString(), pred.toString() }, pred, c);
            }
            if (((BoolValue) bval).val)
            {
              return this.enabled(acts, s0, s1, cm);
            }
            return null;
          }
        }
  }

  protected abstract TLCState enabledUnchanged(SemanticNode expr, ActionItemList acts,
                                          Context c, TLCState s0, TLCState s1, CostModel cm);
  
  protected final TLCState enabledUnchangedImpl(SemanticNode expr, ActionItemList acts,
            Context c, TLCState s0, TLCState s1, CostModel cm) {
	    if (coverage) {cm = cm.get(expr);}
        SymbolNode var = this.getVar(expr, c, true, toolId);
        if (var != null) {
          // a state variable, e.g. UNCHANGED var1
          UniqueString varName = var.getName();
          Value v0 = this.eval(expr, c, s0, s1, EvalControl.Enabled, cm);
          IValue v1 = s1.lookup(varName);
          if (v1 == null) {
            s1 = s1.bind(var, v0);
            return this.enabled(acts, s0, s1, cm);
          }
          if (v1.equals(v0)) {
            return this.enabled(acts, s0, s1, cm);
          }
          MP.printWarning(EC.TLC_UNCHANGED_VARIABLE_CHANGED, new String[]{varName.toString() , expr.toString()});
          return null;
        }

        if (expr instanceof OpApplNode) {
          OpApplNode expr1 = (OpApplNode)expr;
          ExprOrOpArgNode[] args = expr1.getArgs();
          int alen = args.length;
          SymbolNode opNode = expr1.getOperator();
          UniqueString opName = opNode.getName();
          int opcode = BuiltInOPs.getOpCode(opName);

          if (opcode == OPCODE_tup) {
            // a tuple, e.g. UNCHANGED <<var1, var2>>
            if (alen != 0) {
              ActionItemList acts1 = acts;
              for (int i = 1; i < alen; i++) {
                acts1 = (ActionItemList) acts1.cons(args[i], c, cm, IActionItemList.UNCHANGED);
              }
              return this.enabledUnchanged(args[0], acts1, c, s0, s1, cm);
            }
            return this.enabled(acts, s0, s1, cm);
          }

          if (opcode == 0 && alen == 0) {
            // a 0-arity operator:
            Object val = this.lookup(opNode, c, false);

            if (val instanceof LazyValue) {
              LazyValue lv = (LazyValue)val;
              return this.enabledUnchanged(lv.expr, acts, lv.con, s0, s1, cm);
            }
            else if (val instanceof OpDefNode) {
              return this.enabledUnchanged(((OpDefNode)val).getBody(), acts, c, s0, s1, cm);
            }
            else if (val == null) {
              Assert.fail("In computing ENABLED, TLC found the undefined identifier\n" +
                          opName + " in an UNCHANGED expression at\n" + expr, expr ,c);
            }
            return this.enabled(acts, s0, s1, cm);
          }
        }

        final Value v0 = this.eval(expr, c, s0, TLCState.Empty, EvalControl.Enabled, cm);
        // We are in ENABLED and primed but why pass only primed? This appears to
        // be the only place where we call eval from the ENABLED scope without
        // additionally passing EvalControl.Enabled. Not passing Enabled allows a 
        // cached LazyValue could be used (see comments above on line 1384).
        // 
        // The current scope is a nested UNCHANGED in an ENABLED and evaluation is set
        // to primed. However, UNCHANGED e equals e' = e , so anything primed in e
        // becomes double-primed in ENABLED UNCHANGED e. This makes it illegal TLA+
        // which is rejected by SANY's level checking. A perfectly valid spec - where
        // e is not primed - but that also causes this code path to be taken is 23 below:
        // 
        // -------- MODULE 23 ---------
        // VARIABLE t
        // op(var) == var
        // Next == /\ (ENABLED (UNCHANGED op(t)))
        //         /\ (t'= t)
        // Spec == (t = 0) /\ [][Next]_t
        // ============================
        // 
        // However, spec 23 causes the call to this.eval(...) below to throw an
        // EvalException either with EvalControl.Primed. The exception's message is
        // "In evaluation, the identifier t is either undefined or not an operator."
        // indicating that this code path is buggy.
        // 
        // If this bug is ever fixed to make TLC accept spec 23, EvalControl.Primed
        // should likely be rewritten to EvalControl.setPrimed(EvalControl.Enabled)
        // to disable reusage of LazyValues on line ~1384 above.
		final Value v1 = this.eval(expr, c, s1, TLCState.Empty, EvalControl.Primed, cm);
        if (!v0.equals(v1)) {
          return null;
        }
        return this.enabled(acts, s0, s1, cm);
  }

  /* This method determines if the action predicate is valid in (s0, s1). */
  @Override
  public final boolean isValid(Action act, TLCState s0, TLCState s1) {
    Value val = this.eval(act.pred, act.con, s0, s1, EvalControl.Clear, act.cm);
    if (!(val instanceof BoolValue)) {
      Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", act.pred.toString()}, act.pred, act.con);
    }
    return ((BoolValue)val).val;
  }

  /* Returns true iff the predicate is valid in the state. */
  @Override
  public boolean isValid(Action act, TLCState state) {
    return this.isValid(act, state, TLCState.Empty);
  }

  /* Returns true iff the predicate is valid in the state. */
  @Override
  public final boolean isValid(Action act) {
    return this.isValid(act, TLCState.Empty, TLCState.Empty);
  }

    @Override
	public boolean isValid(ExprNode expr, Context ctxt) {
	    IValue val = this.eval(expr, ctxt, TLCState.Empty, TLCState.Empty, 
	    		EvalControl.Const, CostModel.DO_NOT_RECORD);
	    if (!(val instanceof BoolValue)) {
	      Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()}, expr);
	    }
	    return ((BoolValue)val).val;
	}

  @Override
  public final boolean isValid(ExprNode expr) {
	  return isValid(expr, Context.Empty);
  }

  public boolean isValidAssumption(ExprNode assumption) {
	  return isValid(assumption);
  }
  
  @Override
  public final int checkAssumptions() {
      final ExprNode[] assumps = getAssumptions();
      final boolean[] isAxiom = getAssumptionIsAxiom();
      for (int i = 0; i < assumps.length; i++)
      {
          try
          {
              if ((!isAxiom[i]) && !isValidAssumption(assumps[i]))
              {
                  return MP.printError(EC.TLC_ASSUMPTION_FALSE, assumps[i].toString());
              }
          } catch (final Exception e)
          {
              // Assert.printStack(e);
              return MP.printError(EC.TLC_ASSUMPTION_EVALUATION_ERROR,
                      new String[] { assumps[i].toString(), e.getMessage() });
          }
      }
      return EC.NO_ERROR;
  }

	@Override
	public final int checkPostCondition() {
		return checkPostConditionWithContext(Context.Empty);
	}

	@Override
	public final int checkPostConditionWithCounterExample(final IValue value) {
		final SymbolNode def = getCounterExampleDef();
		if (def == null) {
			// TLCExt!CounterExample does not appear anywhere in the spec.
			return checkPostCondition();
		}
		final Context ctxt = Context.Empty.cons(def, value);
		return checkPostConditionWithContext(ctxt);
	}

	private final int checkPostConditionWithContext(final Context ctxt) {
		// User request: http://discuss.tlapl.us/msg03658.html
		final ExprNode[] postConditions = getPostConditionSpecs();
		for (int i = 0; i < postConditions.length; i++) {
			final ExprNode en = postConditions[i];
			try {
				if (!isValid(en, ctxt)) {
					// It's not an assumption because the expression doesn't appear inside
					// an ASSUME, but good enough for this prototype.
					return MP.printError(EC.TLC_ASSUMPTION_FALSE, en.toString());
				}
			} catch (Exception e) {
				// tool.isValid(sn) failed to evaluate...
				return MP.printError(EC.TLC_ASSUMPTION_EVALUATION_ERROR,
						new String[] { en.toString(), e.getMessage() });
			}
		}
		// The PostCheckAssumption/PostCondition cannot be stated as an ordinary
		// invariant
		// with the help of TLCSet/Get because the invariant will only be evaluated for
		// distinct states, but we want it to be evaluated after state-space exploration
		// finished. Hacking away with TLCGet("queue") = 0 doesn't work because the
		// queue
		// can be empty during the evaluation of the next-state relation when a worker
		// dequeues
		// the last state S, that has more successor states.
		return EC.NO_ERROR;
	}
  
    /* Reconstruct the initial state whose fingerprint is fp. */
	@Override
	public final TLCStateInfo getState(final long fp) {
		class InitStateSelectorFunctor implements IStateFunctor {
			private final long fp;
			public TLCState state;
			public InitStateSelectorFunctor(long fp) {
				this.fp = fp;
			}
			@Override
			public Object addElement(TLCState state) {
				if (state == null) {
					return null;
				} else if (this.state != null) {
					// Always return the first match found. Do not let later matches override
					// this.state. This is in line with the original implementation that called
					// getInitStates().
					return null;
				} else if (fp == state.fingerPrint()) {
					this.state = state;
					// TODO Stop generation of initial states preemptively. E.g. make the caller of
					// addElement check for a special return value such as this (the functor).
				}
				return null;
			}
		}
		// Registry a selector that extract out of the (possibly) large set of initial
		// states the one identified by fp. The functor pattern has the advantage
		// compared to this.getInitStates(), that it kind of streams the initial states
		// to the functor whereas getInitStates() stores _all_ init states in a set
		// which is traversed afterwards. This is also consistent with
		// ModelChecker#DoInitFunctor. Using the functor pattern for the processing of
		// init states in ModelChecker#doInit but calling getInitStates() here results
		// in a bug during error trace generation when the set of initial states is too
		// large for getInitStates(). Earlier TLC would have refused to run the model
		// during ModelChecker#doInit.
		final InitStateSelectorFunctor functor = new InitStateSelectorFunctor(fp);
		this.getInitStates(functor);
		final TLCState state = functor.state;
		if (state != null) {
			assert state.isInitial();
			final TLCStateInfo info = new TLCStateInfo(state);
			info.fp = fp;
			return info;
		}
		return null;
	}

  /**
	 * Reconstruct the next state of state s whose fingerprint is fp.
	 *
	 * @return Returns the TLCState wrapped in TLCStateInfo. TLCStateInfo stores
	 *         the stateNumber (relative to the given sinfo) and a pointer to
	 *         the predecessor.
	 */
  @Override
  public final TLCStateInfo getState(long fp, TLCStateInfo sinfo) {
    final TLCStateInfo tlcStateInfo = getState(fp, sinfo.state);
    if (tlcStateInfo == null) {
      throw new EvalException(EC.TLC_FAILED_TO_RECOVER_NEXT);
    }
    tlcStateInfo.stateNumber = sinfo.stateNumber + 1;
    tlcStateInfo.predecessorState = sinfo;
    tlcStateInfo.fp = fp;
    return tlcStateInfo;
  }

  /* Reconstruct the next state of state s whose fingerprint is fp. */
  @Override
  public final TLCStateInfo getState(long fp, TLCState s) {
	  IdThread.setCurrentState(s);
    for (int i = 0; i < this.actions.length; i++) {
      Action curAction = this.actions[i];
      StateVec nextStates = this.getNextStates(curAction, s);
      for (int j = 0; j < nextStates.size(); j++) {
        TLCState state = nextStates.elementAt(j);
        long nfp = state.fingerPrint();
        if (fp == nfp) {
        	state.setPredecessor(s);
        	assert !state.isInitial();
          return new TLCStateInfo(state, curAction);
        }
      }
    }
    return null;
  }

  /* Reconstruct the info for s1.   */
  @Override
  public final TLCStateInfo getState(TLCState s1, TLCState s) {
	  IdThread.setCurrentState(s);
    for (int i = 0; i < this.actions.length; i++) {
      Action curAction = this.actions[i];
      StateVec nextStates = this.getNextStates(curAction, s);
      for (int j = 0; j < nextStates.size(); j++) {
        TLCState state = nextStates.elementAt(j);
        try {
        	if (s1.equals(state)) {
        		state.setPredecessor(s);
        		assert !state.isInitial();
        		return new TLCStateInfo(state, curAction);
        	}
        } catch (TLCRuntimeException e) {
          // s might have two or more successors, whose values are incomparable to the
          // values of s1 (https://github.com/tlaplus/tlaplus/issues/743). Assume s
          // to equal <<"foo", 3>> and its two successor states t1 to equal <<"foo", 4>>
          // and t2 to equal <<TRUE, 5>>. t1 and s1 equal to <<TRUE, 5>> are incomparable. 
          // and t2 to equal <<TRUE, 5>>. t1 and s1 equal to <<TRUE, 5>> are incomparable. 
          // Next ==
          // \/ /\ x' = "foo"
          //    /\ y' = y + 1
          // \/ /\ x' = TRUE
          //    /\ y' = y + 2
        	continue;
        }
      }
    }
    return null;
  }

  /* Return the set of all permutations under the symmetry assumption. */
  @Override
  public final IMVPerm[] getSymmetryPerms() {
    final String name = this.config.getSymmetry();
    if (name.length() == 0) { return null; }
    final Object symm = this.unprocessedDefns.get(name);
    if (symm == null) {
      Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "symmetry function", name});
    }
    if (!(symm instanceof OpDefNode)) {
      Assert.fail("The symmetry function " + name + " must specify a set of permutations.");
    }
    final OpDefNode opDef = (OpDefNode)symm;
    // This calls tlc2.module.TLC.Permutations(Value) and returns a Value of |fcns|
    // = n! where n is the capacity of the symmetry set.
    final IValue fcns = this.eval(opDef.getBody(), Context.Empty, TLCState.Empty, CostModel.DO_NOT_RECORD);
    if (!(fcns instanceof Enumerable) || !(fcns instanceof SetEnumValue)) {
      Assert.fail("The symmetry operator must specify a set of functions.", opDef.getBody());
    }
    final List<Value> values = ((SetEnumValue)fcns).elements().all();
    for (final Value v : values) {
    	if (!(v instanceof FcnRcdValue)) {
    		Assert.fail("The symmetry values must be function records.", opDef.getBody());
    	}
    }
    final ExprOrOpArgNode[] argNodes = ((OpApplNode)opDef.getBody()).getArgs();
    // In the case where the config defines more than one set which is symmetric, they will pass through the
    //		enumerable size() check even if they are single element sets
    final StringBuilder cardinalityOneSetList = new StringBuilder();
    int offenderCount = 0;
    if (argNodes.length >= values.size()) {
    	// If equal, we have as many values as we have permuted sets => we have all 1-element sets;
    	//		if greater than, then we have a heterogenous cardinality of sets, including 0 element sets.
    	for (final ExprOrOpArgNode node : argNodes) {
			addToSubTwoSizedSymmetrySetList(node, cardinalityOneSetList);
			offenderCount++;
    	}
    }
    
    final IMVPerm[] subgroup;
    if (offenderCount == 0) {
        subgroup = MVPerms.permutationSubgroup((Enumerable)fcns);
        final HashSet<ModelValue> subgroupMembers = new HashSet<>();
        for (final IMVPerm imvp : subgroup) {
        	if (imvp instanceof MVPerm) { // should always be the case
        		subgroupMembers.addAll(((MVPerm)imvp).getAllModelValues());
        	}
        }
        for (final ExprOrOpArgNode node : argNodes) {
        	final SetEnumValue enumValue = getSetEnumValueFromArgumentNode(node);
        	
        	if (enumValue != null) {
        		final ValueEnumeration ve = enumValue.elements();
        		
        		boolean found = false;
        		Value v;
        		while ((v = ve.nextElement()) != null) {
        			if ((v instanceof ModelValue) && subgroupMembers.contains(v)) {
        				found = true;
        				break;
        			}
        		}
        		
        		if (!found) {
    				addToSubTwoSizedSymmetrySetList(node, cardinalityOneSetList);
    				offenderCount++;
        		}
        	}
        }
    } else {
    	subgroup = null;
    }
    
    if (offenderCount > 0) {
      final String plurality = (offenderCount > 1) ? "s" : "";
      final String antiPlurality = (offenderCount > 1) ? "" : "s";
      final String toHaveConjugation = (offenderCount > 1) ? "have" : "has";
      
      MP.printWarning(EC.TLC_SYMMETRY_SET_TOO_SMALL,
    		  	  	  new String[] { plurality, cardinalityOneSetList.toString(), toHaveConjugation, antiPlurality });
    }
    
    return subgroup;
  }
  
  /**
   * Teases the original spec name for the set out of node and appends it to the {@code StringBuilder} instance.
   */
  private void addToSubTwoSizedSymmetrySetList(final ExprOrOpArgNode node, final StringBuilder cardinalityOneSetList) {
		final SyntaxTreeNode tn = (SyntaxTreeNode)node.getTreeNode();
		final String image = tn.getHumanReadableImage();
		final String alias;
	    if (image.startsWith(TLAConstants.BuiltInOperators.PERMUTATIONS)) {
		  final int imageLength = image.length();
		  alias = image.substring((TLAConstants.BuiltInOperators.PERMUTATIONS.length() + 1),
				  						  (imageLength - 1));
	    } else {
	    	alias = image;
	    }
		final String specDefinitionName = this.config.getOverridenSpecNameForConfigName(alias);
		final String displayDefinition = (specDefinitionName != null) ? specDefinitionName : alias;
		
		if (cardinalityOneSetList.length() > 0) {
			cardinalityOneSetList.append(", and ");
		}

		cardinalityOneSetList.append(displayDefinition);
  }
  
  /**
   * @param node
   * @return if the node represents a permutation, this will return the {@link SetEnumValue} instance contains its
   * 					model values
   */
  private SetEnumValue getSetEnumValueFromArgumentNode(final ExprOrOpArgNode node) {
	  if (node instanceof OpApplNode) {
		  final OpApplNode permutationNode = (OpApplNode)node;
		  if (permutationNode.getOperator() instanceof OpDefNode) {
			  final OpDefNode operator = (OpDefNode)permutationNode.getOperator();
			  if (TLAConstants.BuiltInOperators.PERMUTATIONS.equals(operator.getName().toString())) {
				  final ExprOrOpArgNode[] operands = permutationNode.getArgs();
				  if ((operands.length == 1)
						  && (operands[0] instanceof OpApplNode)
						  && (((OpApplNode)operands[0]).getOperator() instanceof OpDefOrDeclNode)) {
					  final Object o = ((OpDefOrDeclNode)((OpApplNode)operands[0]).getOperator()).getToolObject(toolId);
					  
					  if (o instanceof SetEnumValue) {
						  return (SetEnumValue)o;
					  } else if (o instanceof WorkerValue) {
						  // If TLC was started with a -workers N specification, N > 1, o will be a WorkerValue instance
						  final WorkerValue wv = (WorkerValue)o;
						  final Object unwrapped = WorkerValue.mux(wv);
						  
						  if (unwrapped instanceof SetEnumValue) {
							  return (SetEnumValue)unwrapped;
						  }
					  }
				  }
			  }
		  }
	  }

	  return null;
  }

  @Override
  public final boolean hasSymmetry() {
    if (this.config == null) {
      return false;
    }
    final String name = this.config.getSymmetry();
    return name.length() > 0;
  }
  @Override
  public final Context getFcnContext(IFcnLambdaValue fcn, ExprOrOpArgNode[] args,
          Context c, TLCState s0, TLCState s1,
          final int control) {
	  return getFcnContext(fcn, args, c, s0, s1, control, CostModel.DO_NOT_RECORD);
  }

  @Override
  public final Context getFcnContext(IFcnLambdaValue fcn, ExprOrOpArgNode[] args,
                                     Context c, TLCState s0, TLCState s1,
                                     final int control, CostModel cm) {
    Context fcon = fcn.getCon();
    int plen = fcn.getParams().length();
    FormalParamNode[][] formals = fcn.getParams().getFormals();
    Value[] domains = (Value[]) fcn.getParams().getDomains();
    boolean[] isTuples = fcn.getParams().isTuples();
    Value argVal = this.eval(args[1], c, s0, s1, control, cm);

    if (plen == 1) {
      if (!domains[0].member(argVal)) {
        Assert.fail("In applying the function\n" + Values.ppr(fcn.toString()) +
                    ",\nthe first argument is:\n" + Values.ppr(argVal.toString()) +
                    "which is not in its domain.\n" + args[0], args[0], c);
      }
      if (isTuples[0]) {
        FormalParamNode[] ids = formals[0];
        TupleValue tv = (TupleValue) argVal.toTuple();
        if (tv == null || argVal.size() != ids.length) {
          Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                      ",\nthe argument is:\n" + Values.ppr(argVal.toString()) +
                      "which does not match its formal parameter.\n" + args[0], args[0], c);
        }
        Value[] elems = tv.elems;
        for (int i = 0; i < ids.length; i++) {
          fcon = fcon.cons(ids[i], elems[i]);
        }
      }
      else {
        fcon = fcon.cons(formals[0][0], argVal);
      }
    }
    else {
      TupleValue tv = (TupleValue) argVal.toTuple();
      if (tv == null) {
        Assert.fail("Attempted to apply a function to an argument not in its" +
                    " domain.\n" + args[0], args[0], c);
      }
      int argn = 0;
      Value[] elems = tv.elems;
      for (int i = 0; i < formals.length; i++) {
        FormalParamNode[] ids = formals[i];
        Value domain = domains[i];
        if (isTuples[i]) {
          if (!domain.member(elems[argn])) {
            Assert.fail("In applying the function\n" + Values.ppr(fcn.toString()) +
                        ",\nthe argument number " + (argn+1) + " is:\n" +
                        Values.ppr(elems[argn].toString()) +
                        "\nwhich is not in its domain.\n" + args[0], args[0], c);
          }
          TupleValue tv1 = (TupleValue) elems[argn++].toTuple();
          if (tv1 == null || tv1.size() != ids.length) {
            Assert.fail("In applying the function\n" + Values.ppr(fcn.toString()) +
                        ",\nthe argument number " + argn + " is:\n" +
                        Values.ppr(elems[argn-1].toString()) +
                        "which does not match its formal parameter.\n" + args[0], args[0], c);
          }
          Value[] avals = tv1.elems;
          for (int j = 0; j < ids.length; j++) {
            fcon = fcon.cons(ids[j], avals[j]);
          }
        }
        else {
          for (int j = 0; j < ids.length; j++) {
            if (!domain.member(elems[argn])) {
              Assert.fail("In applying the function\n" + Values.ppr(fcn.toString()) +
                          ",\nthe argument number " + (argn+1) + " is:\n" +
                          Values.ppr(elems[argn].toString()) +
                          "which is not in its domain.\n" + args[0], args[0], c);
            }
            fcon = fcon.cons(ids[j], elems[argn++]);
          }
        }
      }
    }
    return fcon;
  }

  @Override
  public final IContextEnumerator contexts(OpApplNode appl, Context c, TLCState s0,
          TLCState s1, final int control) {
	  return contexts(appl, c, s0, s1, control, CostModel.DO_NOT_RECORD);
  }

  /* A context enumerator for an operator application. */
  public final ContextEnumerator contexts(OpApplNode appl, Context c, TLCState s0,
                                          TLCState s1, final int control, CostModel cm) {
    return contexts(Ordering.NORMALIZED, appl, c, s0, s1, control, cm);
  }

	private final ContextEnumerator contexts(Ordering ordering, OpApplNode appl, Context c, TLCState s0, TLCState s1, final int control,
			CostModel cm) {
		FormalParamNode[][] formals = appl.getBdedQuantSymbolLists();
	    boolean[] isTuples = appl.isBdedQuantATuple();
	    ExprNode[] domains = appl.getBdedQuantBounds();
	
	    int flen = formals.length;
	    int alen = 0;
	    for (int i = 0; i < flen; i++) {
	      alen += (isTuples[i]) ? 1 : formals[i].length;
	    }
	    Object[] vars = new Object[alen];
	    ValueEnumeration[] enums = new ValueEnumeration[alen];
	    int idx = 0;
	    for (int i = 0; i < flen; i++) {
	      Value boundSet = this.eval(domains[i], c, s0, s1, control, cm);
	      if (!(boundSet instanceof Enumerable)) {
	        Assert.fail("TLC encountered a non-enumerable quantifier bound\n" +
	                    Values.ppr(boundSet.toString()) + ".\n" + domains[i], domains[i], c);
	      }
	      FormalParamNode[] farg = formals[i];
	      if (isTuples[i]) {
	        vars[idx] = farg;
	        enums[idx++] = ((Enumerable)boundSet).elements(ordering);
	      }
	      else {
	        for (int j = 0; j < farg.length; j++) {
	          vars[idx] = farg[j];
	          enums[idx++] = ((Enumerable)boundSet).elements(ordering);
	        }
	      }
	    }
	    return new ContextEnumerator(vars, enums, c);
	}

    // These three are expected by implementing the {@link ITool} interface; they used
    //		to mirror exactly methods that our parent class ({@link Spec}) implemented
    //		however those methods have changed signature with refactoring done for 
    //		Issue #393
	@Override
	public Context getOpContext(OpDefNode odn, ExprOrOpArgNode[] args, Context ctx, boolean b) {
		return getOpContext(odn, args, ctx, b, toolId);
	}
	
	@Override
	public Object lookup(SymbolNode opNode, Context con, boolean b) {
		return lookup(opNode, con, b, toolId);
	}
	
	@Override
	public Object getVal(ExprOrOpArgNode expr, Context con, boolean b) {
		return getVal(expr, con, b, toolId);
	}

	public static boolean isProbabilistic() {
		return PROBABILISTIC;
	}
}
