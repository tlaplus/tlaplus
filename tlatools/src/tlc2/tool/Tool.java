// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Thu  2 Aug 2007 at 10:25:48 PST by lamport
//      modified on Fri Jan  4 22:46:57 PST 2002 by yuanyu

package tlc2.tool;

import java.io.File;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.APSubstInNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LabelNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.LevelConstants;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.util.IdThread;
import tlc2.util.Vect;
import tlc2.value.Applicable;
import tlc2.value.BoolValue;
import tlc2.value.Enumerable;
import tlc2.value.FcnLambdaValue;
import tlc2.value.FcnParams;
import tlc2.value.FcnRcdValue;
import tlc2.value.IValue;
import tlc2.value.LazyValue;
import tlc2.value.MVPerm;
import tlc2.value.MethodValue;
import tlc2.value.OpLambdaValue;
import tlc2.value.OpValue;
import tlc2.value.RecordValue;
import tlc2.value.Reducible;
import tlc2.value.SetCapValue;
import tlc2.value.SetCupValue;
import tlc2.value.SetDiffValue;
import tlc2.value.SetEnumValue;
import tlc2.value.SetOfFcnsValue;
import tlc2.value.SetOfRcdsValue;
import tlc2.value.SetOfTuplesValue;
import tlc2.value.SetPredValue;
import tlc2.value.StringValue;
import tlc2.value.SubsetValue;
import tlc2.value.TupleValue;
import tlc2.value.UnionValue;
import tlc2.value.Value;
import tlc2.value.ValueConstants;
import tlc2.value.ValueEnumeration;
import tlc2.value.ValueExcept;
import tlc2.value.ValueVec;
import tlc2.value.Values;
import util.Assert;
import util.Assert.TLCRuntimeException;
import util.FilenameToStream;
import util.UniqueString;

/**
 * This class provides useful methods for tools like model checker
 * and simulator.
 *
 * It's instance serves as a spec handle
 * This is one of two places in TLC, where not all messages are retrieved from the message printer,
 * but constructed just here in the code.
 */
public class Tool
    extends Spec
    implements ValueConstants, ToolGlobals, TraceApp
{
  protected Action[] actions;     // the list of TLA actions.
  private CallStack callStack;    // the call stack.

  private Vect actionVec = new Vect(10);

  /**
   * Creates a new tool handle
   */
  public Tool(String specFile, String configFile) {
	  this(new File(specFile), specFile, configFile, null);
  }
  
  public Tool(String specFile, String configFile, FilenameToStream resolver) {
	  this(new File(specFile), specFile, configFile, resolver);
  }

  private Tool(File specDir, String specFile, String configFile, FilenameToStream resolver)
  {
	  this(specDir.isAbsolute() ? specDir.getParent() : "", specFile, configFile, resolver);
  }
  
  public Tool(String specDir, String specFile, String configFile, FilenameToStream resolver)
  {
      super(specDir, specFile, configFile, resolver);
      this.actions = null;
      this.callStack = null;
  }

  public Tool(Tool other) {
	  super(other);
	  this.actions = other.actions;
	  this.callStack = other.callStack;
	  this.actionVec = other.actionVec;
  }

  /**
   * Initialization. Any Tool object must call it before doing anything.
   * @param spec - <code>null</code> or a filled spec object from previous SANY run
   */
  public final SpecObj init()
  {
	  return init(true, null);
  }

  public final SpecObj init(boolean preprocess, SpecObj spec)
  {

      // Parse and process this spec.
      // It takes care of all overrides.
      // SZ Feb 20, 2009: added spec reference,
      // if not null it is just used instead of re-parsing
      SpecObj processSpec = super.processSpec(spec);

      // Initialize state.
      TLCStateMut.init(this);

      // Pre-evaluate all the definitions in the spec that are constants.
      if (preprocess) {
          this.processConstantDefns();
      }

      // Finally, process the config file.
      super.processConfig();

      return processSpec;
  }

  public final void setCallStack()
  {
      this.callStack = new CallStack();
  }

  public final CallStack getCallStack()
  {
      return this.callStack;
  }

  /**
   * This method returns the set of all possible actions of the
   * spec, and sets the actions field of this object. In fact, we
   * could simply treat the next predicate as one "giant" action.
   * But for efficiency, we preprocess the next state predicate by
   * splitting it into a set of actions for the maximum prefix
   * of disjunction and existential quantification.
   */
  public final Action[] getActions() {
    if (this.actions == null) {
      Action next = this.getNextStateSpec();
      if (next == null) {
        this.actions = new Action[0];
      }
      else {
        this.getActions(next);
        int sz = this.actionVec.size();
        this.actions = new Action[sz];
        for (int i = 0; i < sz; i++) {
          this.actions[i] = (Action)this.actionVec.elementAt(i);
        }
      }
    }
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
        Assert.fail("The next state relation is not a boolean expression.\n" + next);
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
        int cnt = this.actionVec.size();
        try {
          ContextEnumerator Enum =
            this.contexts(next, con, TLCState.Empty, TLCState.Empty, EvalControl.Clear, cm);
          Context econ;
          while ((econ = Enum.nextElement()) != null) {
            this.getActions(args[0], econ, actionName, cm);
          }
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
  public final StateVec getInitStates() {
	  final StateVec initStates = new StateVec(0);
	  getInitStates(initStates);
	  return initStates;
  }

  public final void getInitStates(IStateFunctor functor) {
	  Vect init = this.getInitStateSpec();
	  ActionItemList acts = ActionItemList.Empty;
      // MAK 09/11/2018: Tail to head iteration order cause the first elem added with
      // acts.cons to be acts tail. This fixes the bug/funny behavior that the init
      // predicate Init == A /\ B /\ C /\ D was evaluated in the order A, D, C, B (A
      // doesn't get added to acts at all).
	  for (int i = (init.size() - 1); i > 0; i--) {
		  Action elem = (Action)init.elementAt(i);
		  acts = acts.cons(elem.pred, elem.con, elem.cm, ActionItemList.PRED);
	  }
	  if (init.size() != 0) {
		  Action elem = (Action)init.elementAt(0);
		  TLCState ps = TLCState.Empty.createEmpty();
		  this.getInitStates(elem.pred, acts, elem.con, ps, functor, elem.cm);
	  }
  }

  /* Create the state specified by pred.  */
  public final TLCState makeState(SemanticNode pred) {
    ActionItemList acts = ActionItemList.Empty;
    TLCState ps = TLCState.Empty.createEmpty();
    StateVec states = new StateVec(0);
    this.getInitStates(pred, acts, Context.Empty, ps, states, acts.cm);
    if (states.size() != 1) {
      Assert.fail("The predicate does not specify a unique state." + pred);
    }
    TLCState state = states.elementAt(0);
    if (!this.isGoodState(state)) {
      Assert.fail("The state specified by the predicate is not complete." + pred);
    }
    return state;
  }

  private final void getInitStates(SemanticNode init, ActionItemList acts,
                                   Context c, TLCState ps, IStateFunctor states, CostModel cm) {
    if (this.callStack != null) this.callStack.push(init);
    try {
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
              c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, coverage ? sub.getCM() : cm));
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
              c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, cm));
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
            Assert.fail("The init state relation is not a boolean expression.\n" + init);
          }
        }
    } catch (TLCRuntimeException | EvalException e) {
	    if (this.callStack != null) {
			// Freeze the callStack to ignore subsequent pop operations. This is
			// necessary to ignore the callStack#pop calls in the finally blocks when the
			// Java call stack gets unwounded.
			this.callStack.freeze();
	    }
	    throw e;
    } finally {
    	if (this.callStack != null) { this.callStack.pop(); }
    }
  }

  private final void getInitStates(ActionItemList acts, TLCState ps, IStateFunctor states, CostModel cm) {
		if (acts.isEmpty()) {
			if (coverage) {
				cm.incInvocations();
				cm.getRoot().incInvocations();
			}
			states.addElement(ps.copy());
			return;
		} else if (ps.allAssigned()) {
			// MAK 05/25/2018: If all values of the initial state have already been
			// assigned, there is no point in further trying to assign values. Instead, all
			// remaining statements (ActionItemList) can just be evaluated for their boolean
			// value.
			// This optimization is especially useful to check inductive invariants which
			// require TLC to generate a very large set of initial states.
			while (!acts.isEmpty()) {
				final IValue bval = this.eval(acts.carPred(), acts.carContext(), ps, TLCState.Empty, EvalControl.Init, acts.cm);
				if (!(bval instanceof BoolValue)) {
					//TODO Choose more fitting error message.
					Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING,
							new String[] { "initial states", "boolean", bval.toString(), acts.pred.toString() });
				}
				if (!((BoolValue) bval).val) {
					return;
				}
				// Move on to the next action in the ActionItemList.
				acts = acts.cdr();
			}
			if (coverage) {
				cm.incInvocations();
				cm.getRoot().incInvocations();
			}
			states.addElement(ps.copy());
			return;
		}
		// Assert.check(act.kind > 0 || act.kind == -1);
		ActionItemList acts1 = acts.cdr();
		this.getInitStates(acts.carPred(), acts1, acts.carContext(), ps, states, acts.cm);
	  }

  private final void getInitStatesAppl(OpApplNode init, ActionItemList acts,
                                       Context c, TLCState ps, IStateFunctor states, CostModel cm) {
    if (this.callStack != null) this.callStack.push(init);
    if (coverage) {cm = cm.get(init);}
    try {
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
              Context c1 = this.getOpContext(opDef, args, c, true, cm);
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
            }
          }
          else {
            if (val instanceof OpValue) {
              Applicable opVal = (Applicable)val;
              IValue[] argVals = new IValue[alen];
              // evaluate the actuals:
              for (int i = 0; i < alen; i++) {
	                argVals[i] = this.eval(args[i], c, ps, TLCState.Empty, EvalControl.Init, cm);
              }
              // apply the operator:
              bval = opVal.apply(argVals, EvalControl.Init);
            }
          }

          if (opcode == 0)
          {
            if (!(bval instanceof BoolValue))
            {
              Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[] { "initial states", "boolean",
                        bval.toString(), init.toString() });
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
              acts = acts.cons(args[i], c, cm, i);
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
                acts1 = acts1.cons(body, c2, cm, ActionItemList.PRED);
              }
              this.getInitStates(body, acts1, c1, ps, states, cm);
            }
            return;
          }
        case OPCODE_ite:    // IfThenElse
          {
            IValue guard = this.eval(args[0], c, ps, TLCState.Empty, EvalControl.Init, cm);
            if (!(guard instanceof BoolValue)) {
              Assert.fail("In computing initial states, a non-boolean expression (" +
                          guard.getKindString() + ") was used as the condition " +
                          "of an IF.\n" + init);
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
                IValue bval = this.eval(pairArgs[0], c, ps, TLCState.Empty, EvalControl.Init, cm);
                if (!(bval instanceof BoolValue)) {
                  Assert.fail("In computing initial states, a non-boolean expression (" +
                              bval.getKindString() + ") was used as a guard condition" +
                              " of a CASE.\n" + pairArgs[1]);
                }
                if (((BoolValue)bval).val) {
                  this.getInitStates(pairArgs[1], acts, c, ps, states, cm);
                  return;
                }
              }
            }
            if (other == null) {
              Assert.fail("In computing initial states, TLC encountered a CASE with no" +
                          " conditions true.\n" + init);
            }
            this.getInitStates(other, acts, c, ps, states, cm);
            return;
          }
        case OPCODE_fa:     // FcnApply
          {
            IValue fval = this.eval(args[0], c, ps, TLCState.Empty, EvalControl.Init, cm);
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
                          fval.getKindString() + ") was applied as a function.\n" + init);
            }
            Applicable fcn = (Applicable) fval;
            IValue argVal = this.eval(args[1], c, ps, TLCState.Empty, EvalControl.Init, cm);
            IValue bval = fcn.apply(argVal, EvalControl.Init);
            if (!(bval instanceof BoolValue))
            {
              Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING2, new String[] { "initial states", "boolean",
                      init.toString() });
            }
            if (((BoolValue)bval).val) {
              this.getInitStates(acts, ps, states, cm);
            }
            return;
          }
        case OPCODE_eq:
          {
            SymbolNode var = this.getVar(args[0], c, false);
            if (var == null || var.getName().getVarLoc() < 0) {
              IValue bval = this.eval(init, c, ps, TLCState.Empty, EvalControl.Init, cm);
              if (!((BoolValue)bval).val) {
                return;
              }
            }
            else {
              UniqueString varName = var.getName();
              IValue lval = ps.lookup(varName);
              IValue rval = this.eval(args[1], c, ps, TLCState.Empty, EvalControl.Init, cm);
              if (lval == null) {
                ps = ps.bind(varName, rval, init);
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
            SymbolNode var = this.getVar(args[0], c, false);
            if (var == null || var.getName().getVarLoc() < 0) {
              IValue bval = this.eval(init, c, ps, TLCState.Empty, EvalControl.Init, cm);
              if (!((BoolValue)bval).val) {
                return;
              }
            }
            else {
              UniqueString varName = var.getName();
              IValue lval = ps.lookup(varName);
              IValue rval = this.eval(args[1], c, ps, TLCState.Empty, EvalControl.Init, cm);
              if (lval == null) {
                if (!(rval instanceof Enumerable)) {
                  Assert.fail("In computing initial states, the right side of \\IN" +
                              " is not enumerable.\n" + init);
                }
                ValueEnumeration Enum = ((Enumerable)rval).elements();
                IValue elem;
                while ((elem = Enum.nextElement()) != null) {
                  ps.bind(varName, elem, init);
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
            IValue lval = this.eval(args[0], c, ps, TLCState.Empty, EvalControl.Init, cm);
            if (!(lval instanceof BoolValue)) {
              Assert.fail("In computing initial states of a predicate of form" +
                          " P => Q, P was " + lval.getKindString() + "\n." + init);
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
            IValue bval = this.eval(init, c, ps, TLCState.Empty, EvalControl.Init, cm);
            if (!(bval instanceof BoolValue)) {

              Assert.fail("In computing initial states, TLC expected a boolean expression," +
                          "\nbut instead found " + bval + ".\n" + init);
            }
            if (((BoolValue)bval).val) {
              this.getInitStates(acts, ps, states, cm);
            }
            return;
          }
        }
    } catch (TLCRuntimeException | EvalException e) {
    	// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context, TLCState, IStateFunctor)
    	if (this.callStack != null) { this.callStack.freeze(); }
	    throw e;
    } finally {
    	if (this.callStack != null) { this.callStack.pop(); }
    }
  }

  /**
   * This method returns the set of next states when taking the action
   * in the given state.
   */
  public final StateVec getNextStates(Action action, TLCState state) {
    ActionItemList acts = ActionItemList.Empty;
    TLCState s1 = TLCState.Empty.createEmpty();
    StateVec nss = new StateVec(0);
    this.getNextStates(action.pred, acts, action.con, state, s1, nss, action.cm);
    if (coverage) { action.cm.incInvocations(nss.size()); }
    return nss;
  }

  private final TLCState getNextStates(SemanticNode pred, ActionItemList acts, Context c,
                                       TLCState s0, TLCState s1, StateVec nss, CostModel cm) {
	    if (this.callStack != null) {
	    	return getNextStatesWithCallStack(pred, acts, c, s0, s1, nss, cm);
	    } else {
	    	return getNextStatesImpl(pred, acts, c, s0, s1, nss, cm);
	    }
  }
  
  private final TLCState getNextStatesWithCallStack(SemanticNode pred, ActionItemList acts, Context c,
              TLCState s0, TLCState s1, StateVec nss, final CostModel cm) {
	    this.callStack.push(pred);
	    try {
	    	return getNextStatesImpl(pred, acts, c, s0, s1, nss, cm);
	    } catch (TLCRuntimeException | EvalException e) {
	    	// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context, TLCState, IStateFunctor)
	    	this.callStack.freeze();
		    throw e;
	    } finally {
	    	this.callStack.pop();
	    }
  }
  
  private final TLCState getNextStatesImpl(SemanticNode pred, ActionItemList acts, Context c,
              TLCState s0, TLCState s1, StateVec nss, CostModel cm) {
    if (coverage) {cm = cm.get(pred);}
        switch (pred.getKind()) {
        case OpApplKind:
          {
            OpApplNode pred1 = (OpApplNode)pred;
            return this.getNextStatesAppl(pred1, acts, c, s0, s1, nss, cm);
          }
        case LetInKind:
          {
            LetInNode pred1 = (LetInNode)pred;
            return this.getNextStates(pred1.getBody(), acts, c, s0, s1, nss, cm);
          }
        case SubstInKind:
          {
            return getNextStatesImplSubstInKind((SubstInNode) pred, acts, c, s0, s1, nss, cm);
          }
        // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
        case APSubstInKind:
          {
            return getNextStatesImplApSubstInKind((APSubstInNode) pred, acts, c, s0, s1, nss, cm);
          }
        // LabelKind class added by LL on 13 Jun 2007
        case LabelKind:
          {
            LabelNode pred1 = (LabelNode)pred;
            return this.getNextStates(pred1.getBody(), acts, c, s0, s1, nss, cm);
          }
        default:
          {
            Assert.fail("The next state relation is not a boolean expression.\n" + pred);
          }
        }
    	return s1;
  }

  private final TLCState getNextStatesImplSubstInKind(SubstInNode pred1, ActionItemList acts, Context c, TLCState s0, TLCState s1, StateVec nss, final CostModel cm) {
  	Subst[] subs = pred1.getSubsts();
  	int slen = subs.length;
  	Context c1 = c;
  	for (int i = 0; i < slen; i++) {
  	  Subst sub = subs[i];
  	  c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, coverage ? sub.getCM() : cm));
  	}
  	return this.getNextStates(pred1.getBody(), acts, c1, s0, s1, nss, cm);
  }
  
  private final TLCState getNextStatesImplApSubstInKind(APSubstInNode pred1, ActionItemList acts, Context c, TLCState s0, TLCState s1, StateVec nss, final CostModel cm) {
  	Subst[] subs = pred1.getSubsts();
  	int slen = subs.length;
  	Context c1 = c;
  	for (int i = 0; i < slen; i++) {
  	  Subst sub = subs[i];
  	  c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, cm));
  	}
  	return this.getNextStates(pred1.getBody(), acts, c1, s0, s1, nss, cm);
  }
  
  private final TLCState getNextStates(ActionItemList acts, final TLCState s0, final TLCState s1,
          final StateVec nss, CostModel cm) {
	  final TLCState copy = getNextStates0(acts, s0, s1, nss, cm);
	  if (coverage && copy != s1) {
		  cm.incInvocations();
	  }
	  return copy;
  }

  private final TLCState getNextStates0(ActionItemList acts, final TLCState s0, final TLCState s1,
                                       final StateVec nss, CostModel cm) {
    if (acts.isEmpty()) {
      nss.addElement(s1);
      return s1.copy();
    } else if (s1.allAssigned()) {
    	return getNextStatesAllAssigned(acts, s0, s1, nss, cm);
    }

    final int kind = acts.carKind();
    SemanticNode pred = acts.carPred();
    Context c = acts.carContext();
    ActionItemList acts1 = acts.cdr();
    cm = acts.cm;
    if (kind > 0) {
      return this.getNextStates(pred, acts1, c, s0, s1, nss, cm);
    }
    else if (kind == -1) {
      return this.getNextStates(pred, acts1, c, s0, s1, nss, cm);
    }
    else if (kind == -2) {
      return this.processUnchanged(pred, acts1, c, s0, s1, nss, cm);
    }
    else {
      IValue v1 = this.eval(pred, c, s0, cm);
      IValue v2 = this.eval(pred, c, s1, cm);
      if (!v1.equals(v2)) {
    	  if (coverage) {
    		  return this.getNextStates(acts1, s0, s1, nss, cm);
    	  } else {
    		  return this.getNextStates0(acts1, s0, s1, nss, cm);
    	  }
      }
    }
    return s1;
  }
  
  private final TLCState getNextStatesAllAssigned(ActionItemList acts, final TLCState s0, final TLCState s1,
		  								final StateVec nss, final CostModel cm) {
	  int kind = acts.carKind();
	  SemanticNode pred = acts.carPred();
	  Context c = acts.carContext();
      CostModel cm2 = acts.cm;
	  while (!acts.isEmpty()) {
		  if (kind > 0 || kind == -1) {
			  final IValue bval = this.eval(pred, c, s0, s1, EvalControl.Clear, cm2);
			  if (!(bval instanceof BoolValue)) {
				  // TODO Choose more fitting error message.
				  Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING,
						  new String[] { "next states", "boolean", bval.toString(), acts.pred.toString() });
			  }
			  if (!((BoolValue) bval).val) {
				  return s1;
			  }
		  } else if (kind == -2) {
			  // Identical to default handling below (line 876). Ignored during this optimization.
			  return this.processUnchanged(pred, acts.cdr(), c, s0, s1, nss, cm2);
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
	  nss.addElement(s1);
	  return s1.copy();
  }

  /* getNextStatesAppl */

  private final TLCState getNextStatesAppl(OpApplNode pred, ActionItemList acts, Context c,
          TLCState s0, TLCState s1, StateVec nss, final CostModel cm) {
	  if (this.callStack != null) {
		  return getNextStatesApplWithCallStack(pred, acts, c, s0, s1, nss, cm);
	  } else {
	      return getNextStatesApplImpl(pred, acts, c, s0, s1, nss, cm);
	  }
  }
  
  private final TLCState getNextStatesApplWithCallStack(OpApplNode pred, ActionItemList acts, Context c,
          TLCState s0, TLCState s1, StateVec nss, final CostModel cm) {
	    this.callStack.push(pred);
	    try {
	    	return getNextStatesApplImpl(pred, acts, c, s0, s1, nss, cm);
	    } catch (TLCRuntimeException | EvalException e) {
	    	// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context, TLCState, IStateFunctor)
	    	this.callStack.freeze();
	    	throw e;
	    } finally {
	    	this.callStack.pop();
	    }
  }

  private final TLCState getNextStatesApplImpl(OpApplNode pred, ActionItemList acts, Context c,
                                           TLCState s0, TLCState s1, StateVec nss, CostModel cm) {
        ExprOrOpArgNode[] args = pred.getArgs();
        int alen = args.length;
        SymbolNode opNode = pred.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        if (opcode == 0) {
          // This is a user-defined operator with one exception: it may
          // be substed by a builtin operator. This special case occurs
          // when the lookup returns an OpDef with opcode # 0.
          Object val = this.lookup(opNode, c, s0, false);

          if (val instanceof OpDefNode) {
            OpDefNode opDef = (OpDefNode)val;
            opcode = BuiltInOPs.getOpCode(opDef.getName());
            if (opcode == 0) {
              // Context c1 = this.getOpContext(opDef, args, c, false);
              Context c1 = this.getOpContext(opDef, args, c, true, cm);
              return this.getNextStates(opDef.getBody(), acts, c1, s0, s1, nss, cm);
            }
          }

          // Added by LL 13 Nov 2009 to fix Yuan's fix
          /*********************************************************************
           * Modified on 23 October 2012 by LL to work if ThmOrAssumpDefNode    *
           * imported with parameterized instantiation.                         *
           *********************************************************************/
          if (val instanceof ThmOrAssumpDefNode) {
            ThmOrAssumpDefNode opDef = (ThmOrAssumpDefNode)val;
            Context c1 = this.getOpContext(opDef, args, c, true);
            return this.getNextStates(opDef.getBody(), acts, c1, s0, s1, nss, cm);
          }

          if (val instanceof LazyValue) {
            LazyValue lv = (LazyValue)val;
            if (lv.getValue() == null || lv.isUncachable()) {
              return this.getNextStates(lv.expr, acts, lv.con, s0, s1, nss, cm);
            }
            val = lv.getValue();
          }

          Object bval = val;
          if (alen == 0) {
            if (val instanceof MethodValue) {
              bval = ((MethodValue)val).apply(EmptyArgs, EvalControl.Clear);
            }
          }
          else {
            if (val instanceof OpValue) {
              Applicable opVal = (Applicable)val;
             IValue[] argVals = new IValue[alen];
              // evaluate the actuals:
              for (int i = 0; i < alen; i++) {
                argVals[i] = this.eval(args[i], c, s0, s1, EvalControl.Clear, cm);
              }
              // apply the operator:
              bval = opVal.apply(argVals, EvalControl.Clear);
            }
          }

          if (opcode == 0)
          {
            if (!(bval instanceof BoolValue))
            {
              Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[] { "next states", "boolean",
                      bval.toString(), pred.toString() });
            }
            if (((BoolValue) bval).val)
            {
          	  if (coverage) {
        		  return this.getNextStates(acts, s0, s1, nss, cm);
          	  } else {
          		  return this.getNextStates0(acts, s0, s1, nss, cm);
          	  }
            }
            return s1;
          }
        }

        TLCState resState = s1;
        switch (opcode) {
        case OPCODE_cl:     // ConjList
        case OPCODE_land:
          {
            ActionItemList acts1 = acts;
            for (int i = alen - 1; i > 0; i--) {
              acts1 = acts1.cons(args[i], c, cm, i);
            }
            return this.getNextStates(args[0], acts1, c, s0, s1, nss, cm);
          }
        case OPCODE_dl:     // DisjList
        case OPCODE_lor:
          {
            for (int i = 0; i < alen; i++) {
              resState = this.getNextStates(args[i], acts, c, s0, resState, nss, cm);
            }
            return resState;
          }
        case OPCODE_be:     // BoundedExists
          {
            SemanticNode body = args[0];
            ContextEnumerator Enum = this.contexts(pred, c, s0, s1, EvalControl.Clear, cm);
            Context c1;
            while ((c1 = Enum.nextElement()) != null) {
              resState = this.getNextStates(body, acts, c1, s0, resState, nss, cm);
            }
            return resState;
          }
        case OPCODE_bf:     // BoundedForall
          {
            SemanticNode body = args[0];
            ContextEnumerator Enum = this.contexts(pred, c, s0, s1, EvalControl.Clear, cm);
            Context c1 = Enum.nextElement();
            if (c1 == null) {
              resState = this.getNextStates(acts, s0, s1, nss, cm);
            }
            else {
              ActionItemList acts1 = acts;
              Context c2;
              while ((c2 = Enum.nextElement()) != null) {
                acts1 = acts1.cons(body, c2, cm, ActionItemList.PRED);
              }
              resState = this.getNextStates(body, acts1, c1, s0, s1, nss, cm);
            }
            return resState;
          }
        case OPCODE_fa:     // FcnApply
          {
            IValue fval = this.eval(args[0], c, s0, s1, EvalControl.KeepLazy, cm);
            if (fval instanceof FcnLambdaValue) {
              FcnLambdaValue fcn = (FcnLambdaValue)fval;
              if (fcn.fcnRcd == null) {
                Context c1 = this.getFcnContext(fcn, args, c, s0, s1, EvalControl.Clear, cm);
                return this.getNextStates(fcn.body, acts, c1, s0, s1, nss, cm);
              }
              fval = fcn.fcnRcd;
            }
            if (!(fval instanceof Applicable)) {
              Assert.fail("In computing next states, a non-function (" +
                          fval.getKindString() + ") was applied as a function.\n" + pred);
            }
            Applicable fcn = (Applicable)fval;
            IValue argVal = this.eval(args[1], c, s0, s1, EvalControl.Clear, cm);
            IValue bval = fcn.apply(argVal, EvalControl.Clear);
            if (!(bval instanceof BoolValue)) {
              Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING2, new String[] { "next states", "boolean",
                      pred.toString() });
            }
            if (((BoolValue)bval).val) {
              return this.getNextStates(acts, s0, s1, nss, cm);
            }
            return resState;
          }
        case OPCODE_aa:     // AngleAct <A>_e
          {
            ActionItemList acts1 = acts.cons(args[1], c, cm, ActionItemList.CHANGED);
            return this.getNextStates(args[0], acts1, c, s0, s1, nss, cm);
          }
        case OPCODE_sa:     // [A]_e
          {
            /* The following two lines of code did not work, and were changed by
             * YuanYu to mimic the way \/ works.  Change made
             *  11 Mar 2009, with LL sitting next to him.
             */
              //    this.getNextStates(args[0], acts, c, s0, s1, nss);
              //    return this.processUnchanged(args[1], acts, c, s0, s1, nss);
            resState = this.getNextStates(args[0], acts, c, s0, resState, nss, cm);
            return this.processUnchanged(args[1], acts, c, s0, resState, nss, cm);
          }
        case OPCODE_ite:    // IfThenElse
          {
            IValue guard = this.eval(args[0], c, s0, s1, EvalControl.Clear, cm);
            if (!(guard instanceof BoolValue)) {
              Assert.fail("In computing next states, a non-boolean expression (" +
                          guard.getKindString() + ") was used as the condition of" +
                          " an IF." + pred);
            }
            if (((BoolValue)guard).val) {
              return this.getNextStates(args[1], acts, c, s0, s1, nss, cm);
            }
            else {
              return this.getNextStates(args[2], acts, c, s0, s1, nss, cm);
            }
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
                IValue bval = this.eval(pairArgs[0], c, s0, s1, EvalControl.Clear, coverage ? cm.get(args[i]) : cm);
                if (!(bval instanceof BoolValue)) {
                  Assert.fail("In computing next states, a non-boolean expression (" +
                              bval.getKindString() + ") was used as a guard condition" +
                              " of a CASE.\n" + pairArgs[1]);
                }
                if (((BoolValue)bval).val) {
                  return this.getNextStates(pairArgs[1], acts, c, s0, s1, nss, coverage ? cm.get(args[i]) : cm);
                }
              }
            }
            if (other == null) {
              Assert.fail("In computing next states, TLC encountered a CASE with no" +
                          " conditions true.\n" + pred);
            }
            return this.getNextStates(other, acts, c, s0, s1, nss, coverage ? cm.get(args[alen - 1]) : cm);
          }
        case OPCODE_eq:
          {
            SymbolNode var = this.getPrimedVar(args[0], c, false);
            // Assert.check(var.getName().getVarLoc() >= 0);
            if (var == null) {
              IValue bval = this.eval(pred, c, s0, s1, EvalControl.Clear, cm);
              if (!((BoolValue)bval).val) {
                return resState;
              }
            }
            else {
              UniqueString varName = var.getName();
              IValue lval = s1.lookup(varName);
              IValue rval = this.eval(args[1], c, s0, s1, EvalControl.Clear, cm);
              if (lval == null) {
                resState.bind(varName, rval, pred);
                resState = this.getNextStates(acts, s0, resState, nss, cm);
                resState.unbind(varName);
                return resState;
              }
              else if (!lval.equals(rval)) {
                return resState;
              }
            }
            return this.getNextStates(acts, s0, s1, nss, cm);
          }
        case OPCODE_in:
          {
            SymbolNode var = this.getPrimedVar(args[0], c, false);
            // Assert.check(var.getName().getVarLoc() >= 0);
            if (var == null) {
              IValue bval = this.eval(pred, c, s0, s1, EvalControl.Clear, cm);
              if (!((BoolValue)bval).val) {
                return resState;
              }
            }
            else {
              UniqueString varName = var.getName();
              IValue lval = s1.lookup(varName);
              IValue rval = this.eval(args[1], c, s0, s1, EvalControl.Clear, cm);
              if (lval == null) {
                if (!(rval instanceof Enumerable)) {
                  Assert.fail("In computing next states, the right side of \\IN" +
                              " is not enumerable.\n" + pred);
                }
                ValueEnumeration Enum = ((Enumerable)rval).elements();
                IValue elem;
                while ((elem = Enum.nextElement()) != null) {
                  resState.bind(varName, elem, pred);
                  resState = this.getNextStates(acts, s0, resState, nss, cm);
                  resState.unbind(varName);
                }
                return resState;
              }
              else if (!rval.member(lval)) {
                return resState;
              }
            }
            return this.getNextStates(acts, s0, s1, nss, cm);
          }
        case OPCODE_implies:
          {
            IValue bval = this.eval(args[0], c, s0, s1, EvalControl.Clear, cm);
            if (!(bval instanceof BoolValue)) {
              Assert.fail("In computing next states of a predicate of the form" +
                          " P => Q, P was\n" + bval.getKindString() + ".\n" + pred);
            }
            if (((BoolValue)bval).val) {
              return this.getNextStates(args[1], acts, c, s0, s1, nss, cm);
            }
            else {
              return this.getNextStates(acts, s0, s1, nss, cm);
            }
          }
        case OPCODE_unchanged:
          {
            return this.processUnchanged(args[0], acts, c, s0, s1, nss, cm);
          }
        case OPCODE_cdot:
          {
            Assert.fail("The current version of TLC does not support action composition.");
            /***
            TLCState s01 = TLCStateFun.Empty;
            StateVec iss = new StateVec(0);
            this.getNextStates(args[0], ActionItemList.Empty, c, s0, s01, iss);
            int sz = iss.size();
            for (int i = 0; i < sz; i++) {
              s01 = iss.elementAt(i);
              this.getNextStates(args[1], acts, c, s01, s1, nss);
            }
            ***/
            return s1;
          }
        // The following case added by LL on 13 Nov 2009 to handle subexpression names.
        case OPCODE_nop:
        {
            return this.getNextStates(args[0], acts, c, s0, s1, nss, cm);
        }
        default:
          {
            // We handle all the other builtin operators here.
            IValue bval = this.eval(pred, c, s0, s1, EvalControl.Clear, cm);
            if (!(bval instanceof BoolValue)) {
              Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[] { "next states", "boolean",
                      bval.toString(), pred.toString() });
            }
            if (((BoolValue)bval).val) {
              resState = this.getNextStates(acts, s0, s1, nss, cm);
            }
            return resState;
          }
        }
  }
  
  /* processUnchanged */

  private final TLCState processUnchanged(SemanticNode expr, ActionItemList acts, Context c,
                                          TLCState s0, TLCState s1, StateVec nss, CostModel cm) {
	  if (this.callStack != null) {
		  return processUnchangedWithCallStack(expr, acts, c, s0, s1, nss, cm);
	  } else {
		   return processUnchangedImpl(expr, acts, c, s0, s1, nss, cm);
	  }
  }
  private final TLCState processUnchangedWithCallStack(SemanticNode expr, ActionItemList acts, Context c,
          TLCState s0, TLCState s1, StateVec nss, CostModel cm) {
	   this.callStack.push(expr);
	   try {
		   return processUnchangedImpl(expr, acts, c, s0, s1, nss, cm);
	    } catch (TLCRuntimeException | EvalException e) {
	    	// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context, TLCState, IStateFunctor)
	    	this.callStack.freeze();
	    	throw e;
	    } finally {
	    	this.callStack.pop();
	    }
  }
  private final TLCState processUnchangedImpl(SemanticNode expr, ActionItemList acts, Context c,
          TLCState s0, TLCState s1, StateVec nss, CostModel cm) {
    if (coverage){cm = cm.get(expr);}
        SymbolNode var = this.getVar(expr, c, false);
        TLCState resState = s1;
        if (var != null) {
            return processUnchangedImplVar(expr, acts, s0, s1, nss, var, cm);
        }

        if (expr instanceof OpApplNode) {
          OpApplNode expr1 = (OpApplNode)expr;
          ExprOrOpArgNode[] args = expr1.getArgs();
          int alen = args.length;
          SymbolNode opNode = expr1.getOperator();
          UniqueString opName = opNode.getName();
          int opcode = BuiltInOPs.getOpCode(opName);

          if (opcode == OPCODE_tup) {
            return processUnchangedImplTuple(acts, c, s0, s1, nss, args, alen, cm, coverage ? cm.get(expr1) : cm);
          }

          if (opcode == 0 && alen == 0) {
            // a 0-arity operator:
            return processUnchangedImpl0Arity(expr, acts, c, s0, s1, nss, cm, opNode, opName);
          }
        }

        IValue v0 = this.eval(expr, c, s0, cm);
        IValue v1 = this.eval(expr, c, s1, null, EvalControl.Clear, cm);
        if (v0.equals(v1)) {
          resState = this.getNextStates(acts, s0, s1, nss, cm);
        }
        return resState;
  }

  private final TLCState processUnchangedImpl0Arity(final SemanticNode expr, final ActionItemList acts,
			final Context c, final TLCState s0, final TLCState s1, final StateVec nss, final CostModel cm,
			final SymbolNode opNode, final UniqueString opName) {
		final Object val = this.lookup(opNode, c, false);
	
		if (val instanceof OpDefNode) {
		  return this.processUnchanged(((OpDefNode)val).getBody(), acts, c, s0, s1, nss, cm);
		}
		else if (val instanceof LazyValue) {
		  final LazyValue lv = (LazyValue)val;
		  return this.processUnchanged(lv.expr, acts, lv.con, s0, s1, nss, cm);
		}
		else {
		  Assert.fail("In computing next states, TLC found the identifier\n" +
		              opName + " undefined in an UNCHANGED expression at\n" + expr);
		}
		return this.getNextStates(acts, s0, s1, nss, cm);
  }

  public final IValue eval(SemanticNode expr, Context c, TLCState s0) {
	    return this.eval(expr, c, s0, TLCState.Empty, EvalControl.Clear, CostModel.DO_NOT_RECORD);
	  }

  private final TLCState processUnchangedImplTuple(ActionItemList acts, Context c, TLCState s0, TLCState s1, StateVec nss,
  		ExprOrOpArgNode[] args, int alen, CostModel cm, CostModel cmNested) {
  	// a tuple:
  	if (alen != 0) {
  	  ActionItemList acts1 = acts;
  	  for (int i = alen-1; i > 0; i--) {
  	    acts1 = acts1.cons(args[i], c, cmNested, ActionItemList.UNCHANGED);
  	  }
  	  return this.processUnchanged(args[0], acts1, c, s0, s1, nss, cmNested);
  	}
  	return this.getNextStates(acts, s0, s1, nss, cm);
  }
  
  private final TLCState processUnchangedImplVar(SemanticNode expr, ActionItemList acts, TLCState s0, TLCState s1, StateVec nss,
  		SymbolNode var, final CostModel cm) {
          TLCState resState = s1;
          // expr is a state variable:
          final UniqueString varName = var.getName();
          final IValue val0 = s0.lookup(varName);
          final IValue val1 = s1.lookup(varName);
          if (val1 == null) {
		  	resState.bind(varName, val0, expr);
            if (coverage) {
            	resState = this.getNextStates(acts, s0, resState, nss, cm);
            } else {
            	resState = this.getNextStates0(acts, s0, resState, nss, cm);
            }
		  	resState.unbind(varName);
          }
          else if (val0.equals(val1)) {
              if (coverage) {
                  resState = this.getNextStates(acts, s0, s1, nss, cm);
              } else {
                  resState = this.getNextStates0(acts, s0, s1, nss, cm);
              }
          }
          else {
        	  MP.printWarning(EC.TLC_UNCHANGED_VARIABLE_CHANGED, new String[]{varName.toString(), expr.toString()});
          }
          return resState;
  }
    
  /* eval */

  /* Special version of eval for state expressions. */
  public final IValue eval(SemanticNode expr, Context c, TLCState s0, CostModel cm) {
    return this.eval(expr, c, s0, TLCState.Empty, EvalControl.Clear, cm);
  }
  
	  public final IValue eval(SemanticNode expr, Context c, TLCState s0,
              TLCState s1, final int control) {
		  return eval(expr, c, s0, s1, control, CostModel.DO_NOT_RECORD);
	  }
  /*
   * This method evaluates the expression expr in the given context,
   * current state, and partial next state.
   */
  public final IValue eval(SemanticNode expr, Context c, TLCState s0,
                          TLCState s1, final int control, final CostModel cm) {
	    if (this.callStack != null) {
	    	return evalWithCallStack(expr, c, s0, s1, control, cm);
	    } else {
	    	return evalImpl(expr, c, s0, s1, control, cm);
	    }
  }
  private final IValue evalWithCallStack(SemanticNode expr, Context c, TLCState s0,
          TLCState s1, final int control, final CostModel cm) {
	    this.callStack.push(expr);
	    try {
	    	return evalImpl(expr, c, s0, s1, control, cm);
	    } catch (TLCRuntimeException | EvalException e) {
	    	// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context, TLCState, IStateFunctor)
	    	this.callStack.freeze();
	    	throw e;
	    } finally {
	    	this.callStack.pop();
	    }
  }
  
  private final IValue evalImpl(final SemanticNode expr, final Context c, final TLCState s0,
          final TLCState s1, final int control, CostModel cm) {
    if (coverage) {cm = cm.get(expr);}
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
            return Values.getValue(expr);
          }
        case AtNodeKind:
          {
            return (IValue)c.lookup(EXCEPT_AT);
          }
        case OpArgKind:
          {
            return evalImplOpArgKind((OpArgNode) expr, c, s0, s1, cm);
          }
        default:
          {
            Assert.fail("Attempted to evaluate an expression that cannot be evaluated.\n" +
                        expr);
            return null;     // make compiler happy
          }
        }
  }

  private final IValue evalImplLetInKind(LetInNode expr1, Context c, TLCState s0, TLCState s1, final int control, final CostModel cm) {
	OpDefNode[] letDefs = expr1.getLets();
	int letLen = letDefs.length;
	Context c1 = c;
	for (int i = 0; i < letLen; i++) {
	  OpDefNode opDef = letDefs[i];
	  if (opDef.getArity() == 0) {
	    IValue rhs = new LazyValue(opDef.getBody(), c1, cm);
	    c1 = c1.cons(opDef, rhs);
	  }
	}
	return this.eval(expr1.getBody(), c1, s0, s1, control, cm);
  }

  private final IValue evalImplSubstInKind(SubstInNode expr1, Context c, TLCState s0, TLCState s1, final int control, final CostModel cm) {
  	Subst[] subs = expr1.getSubsts();
  	int slen = subs.length;
  	Context c1 = c;
  	for (int i = 0; i < slen; i++) {
  	  Subst sub = subs[i];
  	  c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true, coverage ? sub.getCM() : cm));
  	}
  	return this.eval(expr1.getBody(), c1, s0, s1, control, cm);
  }
    
  private final IValue evalImplApSubstInKind(APSubstInNode expr1, Context c, TLCState s0, TLCState s1, final int control, final CostModel cm) {
  	Subst[] subs = expr1.getSubsts();
  	int slen = subs.length;
  	Context c1 = c;
  	for (int i = 0; i < slen; i++) {
  	  Subst sub = subs[i];
  	  c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true, cm));
  	}
  	return this.eval(expr1.getBody(), c1, s0, s1, control, cm);
  }
  
  private final IValue evalImplOpArgKind(OpArgNode expr1, Context c, TLCState s0, TLCState s1, final CostModel cm) {
  	SymbolNode opNode = expr1.getOp();
  	Object val = this.lookup(opNode, c, false);
  	if (val instanceof OpDefNode) {
  	  return setSource(expr1, new OpLambdaValue((OpDefNode)val, this, c, s0, s1, cm));
  	}
  	return (IValue)val;
  }
  
  /* evalAppl */
  
  private final IValue evalAppl(final OpApplNode expr, Context c, TLCState s0,
          TLCState s1, final int control, final CostModel cm) {
	  if (this.callStack != null) {
		  return evalApplWithCallStack(expr, c, s0, s1, control, cm);
	  } else {
		  return evalApplImpl(expr, c, s0, s1, control, cm);
	  }
  }

  private final IValue evalApplWithCallStack(final OpApplNode expr, Context c, TLCState s0,
          TLCState s1, final int control, final CostModel cm) {
	    this.callStack.push(expr);
	    try {
	    	return evalApplImpl(expr, c, s0, s1, control, cm);
	    } catch (TLCRuntimeException | EvalException e) {
	    	// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context, TLCState, IStateFunctor)
	    	this.callStack.freeze();
	    	throw e;
	    } finally {
	    	this.callStack.pop();
	    }
  }
  
  private final IValue evalApplImpl(final OpApplNode expr, Context c, TLCState s0,
                              TLCState s1, final int control, CostModel cm) {
    if (coverage){
    	cm = cm.get(expr);
    	cm.incInvocations();
    }
        ExprOrOpArgNode[] args = expr.getArgs();
        SymbolNode opNode = expr.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        if (opcode == 0) {
          // This is a user-defined operator with one exception: it may
          // be substed by a builtin operator. This special case occurs
          // when the lookup returns an OpDef with opcode # 0.
          Object val = this.lookup(opNode, c, s0, EvalControl.isPrimed(control));

          // First, unlazy if it is a lazy value. We cannot use the cached
          // value when s1 == null or isEnabled(control).
			if (val instanceof LazyValue) {
				final LazyValue lv = (LazyValue) val;
				if (s1 == null) {
					val = this.eval(lv.expr, lv.con, s0, null, control, lv.getCostModel());
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
						final IValue res = this.eval(lv.expr, lv.con, s0, s1, control, lv.getCostModel());
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

			IValue res = null;
          if (val instanceof OpDefNode) {
            OpDefNode opDef = (OpDefNode)val;
            opcode = BuiltInOPs.getOpCode(opDef.getName());
            if (opcode == 0) {
              Context c1 = this.getOpContext(opDef, args, c, true, cm);
              res = this.eval(opDef.getBody(), c1, s0, s1, control, cm);
            }
          }
          else if (val instanceof IValue) {
            res = (IValue)val;
            int alen = args.length;
            if (alen == 0) {
              if (val instanceof MethodValue) {
                res = ((MethodValue)val).apply(EmptyArgs, EvalControl.Clear);
              }
            }
            else {
              if (val instanceof OpValue) {
                Applicable opVal = (Applicable)val;
                IValue[] argVals = new IValue[alen];
                // evaluate the actuals:
                for (int i = 0; i < alen; i++) {
                  argVals[i] = this.eval(args[i], c, s0, s1, control, cm);
                }
                // apply the operator:
                res = opVal.apply(argVals, control);
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
            Assert.fail(EC.TLC_CONFIG_UNDEFINED_OR_NO_OPERATOR,
                new String[] { opNode.getName().toString(), expr.toString() });
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
            IValue inVal = this.eval(inExpr, c, s0, s1, control, cm);
            if (!(inVal instanceof Enumerable)) {
              Assert.fail("Attempted to compute the value of an expression of\n" +
                          "form CHOOSE x \\in S: P, but S was not enumerable.\n" + expr);
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
              IValue val;
              while ((val = enumSet.nextElement()) != null) {
                TupleValue tv = (TupleValue) val.toTuple();
                if (tv == null || tv.size() != cnt) {
                  Assert.fail("Attempted to compute the value of an expression of form\n" +
                              "CHOOSE <<x1, ... , xN>> \\in S: P, but S was not a set\n" +
                              "of N-tuples.\n" + expr);
                }
                Context c1 = c;
                for (int i = 0; i < cnt; i++) {
                  c1 = c1.cons(bvars[i], tv.elems[i]);
                }
                IValue bval = this.eval(pred, c1, s0, s1, control, cm);
                if (!(bval instanceof BoolValue)) {
                  Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()});
                }
                if (((BoolValue)bval).val) {
                  return val;
                }
              }
            }
            else {
              // Simple identifier case:
              SymbolNode name = bvars[0];
              IValue val;
              while ((val = enumSet.nextElement()) != null) {
                Context c1 = c.cons(name, val);
                IValue bval = this.eval(pred, c1, s0, s1, control, cm);
                if (!(bval instanceof BoolValue)) {
                  Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()});
                }
                if (((BoolValue)bval).val) {
                  return val;
                }
              }
            }
            Assert.fail("Attempted to compute the value of an expression of form\n" +
                        "CHOOSE x \\in S: P, but no element of S satisfied P.\n" + expr);
            return null;    // make compiler happy
          }
        case OPCODE_be:     // BoundedExists
          {
            ContextEnumerator Enum = this.contexts(expr, c, s0, s1, control, cm);
            SemanticNode body = args[0];
            Context c1;
            while ((c1 = Enum.nextElement()) != null) {
              IValue bval = this.eval(body, c1, s0, s1, control, cm);
              if (!(bval instanceof BoolValue)) {
                Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()});
              }
              if (((BoolValue)bval).val) {
                return ValTrue;
              }
            }
            return ValFalse;
          }
        case OPCODE_bf:     // BoundedForall
          {
            ContextEnumerator Enum = this.contexts(expr, c, s0, s1, control, cm);
            SemanticNode body = args[0];
            Context c1;
            while ((c1 = Enum.nextElement()) != null) {
              IValue bval = this.eval(body, c1, s0, s1, control, cm);
              if (!(bval instanceof BoolValue)) {
                Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()});
              }
              if (!((BoolValue)bval).val) {
                return ValFalse;
              }
            }
            return ValTrue;
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
              }
              else {
                IValue bval = this.eval(pairArgs[0], c, s0, s1, control, coverage ? cm.get(pairNode) : cm);
                if (!(bval instanceof BoolValue)) {
                  Assert.fail("A non-boolean expression (" + bval.getKindString() +
                              ") was used as a condition of a CASE. " + pairArgs[0]);
                }
                if (((BoolValue)bval).val) {
                  return this.eval(pairArgs[1], c, s0, s1, control, coverage ? cm.get(pairNode) : cm);
                }
              }
            }
            if (other == null) {
              Assert.fail("Attempted to evaluate a CASE with no conditions true.\n" + expr);
            }
            return this.eval(other, c, s0, s1, control, cm);
          }
        case OPCODE_cp:     // CartesianProd
          {
            int alen = args.length;
            IValue[] sets = new IValue[alen];
            for (int i = 0; i < alen; i++) {
              sets[i] = this.eval(args[i], c, s0, s1, control, cm);
            }
            return setSource(expr, new SetOfTuplesValue(sets, cm));
          }
        case OPCODE_cl:     // ConjList
          {
            int alen = args.length;
            for (int i = 0; i < alen; i++) {
              IValue bval = this.eval(args[i], c, s0, s1, control, cm);
              if (!(bval instanceof BoolValue)) {
                Assert.fail("A non-boolean expression (" + bval.getKindString() +
                            ") was used as a formula in a conjunction.\n" + args[i]);
              }
              if (!((BoolValue)bval).val) {
                return ValFalse;
              }
            }
            return ValTrue;
          }
        case OPCODE_dl:     // DisjList
          {
            int alen = args.length;
            for (int i = 0; i < alen; i++) {
              IValue bval = this.eval(args[i], c, s0, s1, control, cm);
              if (!(bval instanceof BoolValue)) {
                Assert.fail("A non-boolean expression (" + bval.getKindString() +
                            ") was used as a formula in a disjunction.\n" + args[i]);
              }
              if (((BoolValue)bval).val) {
                return ValTrue;
              }
            }
            return ValFalse;
          }
        case OPCODE_exc:    // Except
          {
            int alen = args.length;
            IValue result = this.eval(args[0], c, s0, s1, control, cm);
            // SZ: variable not used ValueExcept[] expts = new ValueExcept[alen-1];
            for (int i = 1; i < alen; i++) {
              OpApplNode pairNode = (OpApplNode)args[i];
              ExprOrOpArgNode[] pairArgs = pairNode.getArgs();
              SemanticNode[] cmpts = ((OpApplNode)pairArgs[0]).getArgs();

              IValue[] lhs = new IValue[cmpts.length];
              for (int j = 0; j < lhs.length; j++) {
                lhs[j] = this.eval(cmpts[j], c, s0, s1, control,  coverage ? cm.get(pairNode).get(pairArgs[0]) : cm);
              }
              IValue atVal = result.select(lhs);
              if (atVal == null) {
                // Do nothing but warn:
                  MP.printWarning(EC.TLC_EXCEPT_APPLIED_TO_UNKNOWN_FIELD, new String[]{args[0].toString()});
              }
              else {
                Context c1 = c.cons(EXCEPT_AT, atVal);
                IValue rhs = this.eval(pairArgs[1], c1, s0, s1, control,  coverage ? cm.get(pairNode) : cm);
                ValueExcept vex = new ValueExcept(lhs, rhs);
                result = result.takeExcept(vex);
              }
            }
            return result;
          }
        case OPCODE_fa:     // FcnApply
          {
            IValue result = null;
            IValue fval = this.eval(args[0], c, s0, s1, EvalControl.setKeepLazy(control), cm);
            if ((fval instanceof FcnRcdValue) ||
                (fval instanceof FcnLambdaValue)) {
              Applicable fcn = (Applicable)fval;
              IValue argVal = this.eval(args[1], c, s0, s1, control, cm);
              result = fcn.apply(argVal, control);
            }
            else if ((fval instanceof TupleValue) ||
                     (fval instanceof RecordValue)) {
              Applicable fcn = (Applicable)fval;
              if (args.length != 2) {
                Assert.fail("Attempted to evaluate an expression of form f[e1, ... , eN]" +
                            "\nwith f a tuple or record and N > 1.\n" + expr);
              }
              IValue aval = this.eval(args[1], c, s0, s1, control, cm);
              result = fcn.apply(aval, control);
            }
            else {
              Assert.fail("A non-function (" + fval.getKindString() + ") was applied" +
                          " as a function.\n" + expr);
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

            IValue[] dvals = new IValue[domains.length];
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
              return fval.toFcnRcd();
            }
            return fval;
          }
        case OPCODE_ite:    // IfThenElse
          {
            IValue bval = this.eval(args[0], c, s0, s1, control, cm);
            if (!(bval instanceof BoolValue)) {
              Assert.fail("A non-boolean expression (" + bval.getKindString() +
                          ") was used as the condition of an IF.\n" + expr);
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
            IValue[] vals = new IValue[alen];
            for (int i = 0; i < alen; i++) {
              OpApplNode pairNode = (OpApplNode)args[i];
              ExprOrOpArgNode[] pair = pairNode.getArgs();
              names[i] = ((StringValue)Values.getValue(pair[0])).getVal();
              vals[i] = this.eval(pair[1], c, s0, s1, control, coverage ? cm.get(pairNode) : cm);
            }
            return setSource(expr, new RecordValue(names, vals, false, cm));
          }
        case OPCODE_rs:     // RcdSelect
          {
            IValue rval = this.eval(args[0], c, s0, s1, control, cm);
            IValue sval = Values.getValue(args[1]);
            if (rval instanceof RecordValue) {
              IValue result = ((RecordValue)rval).select(sval);
              if (result == null) {
                Assert.fail("Attempted to select nonexistent field " + sval + " from the" +
                            " record\n" + Values.ppr(rval.toString()) + "\n" + expr);
              }
              return result;
            }
            else {
              FcnRcdValue fcn = (FcnRcdValue) rval.toFcnRcd();
              if (fcn == null) {
                Assert.fail("Attempted to select field " + sval + " from a non-record" +
                            " value " + Values.ppr(rval.toString()) + "\n" + expr);
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
              IValue val = this.eval(body, c1, s0, s1, control, cm);
              vals.addElement(val);
              // vals.addElement1(val);
            }
            return setSource(expr, new SetEnumValue(vals, false, cm));
          }
        case OPCODE_sor:    // SetOfRcds
          {
            int alen = args.length;
            UniqueString names[] = new UniqueString[alen];
            IValue vals[] = new IValue[alen];
            for (int i = 0; i < alen; i++) {
              OpApplNode pairNode = (OpApplNode)args[i];
              ExprOrOpArgNode[] pair = pairNode.getArgs();
              names[i] = ((StringValue)Values.getValue(pair[0])).getVal();
              vals[i] = this.eval(pair[1], c, s0, s1, control, coverage ? cm.get(pairNode) : cm);
            }
            return setSource(expr, new SetOfRcdsValue(names, vals, false, cm));
          }
        case OPCODE_sof:    // SetOfFcns
          {
            IValue lhs = this.eval(args[0], c, s0, s1, control, cm);
            IValue rhs = this.eval(args[1], c, s0, s1, control, cm);
            return setSource(expr, new SetOfFcnsValue(lhs, rhs, cm));
          }
        case OPCODE_sso:    // SubsetOf
          {
            SemanticNode pred = args[0];
            SemanticNode inExpr = expr.getBdedQuantBounds()[0];
            IValue inVal = this.eval(inExpr, c, s0, s1, control, cm);
            boolean isTuple = expr.isBdedQuantATuple()[0];
            FormalParamNode[] bvars = expr.getBdedQuantSymbolLists()[0];
            if (inVal instanceof Reducible) {
              ValueVec vals = new ValueVec();
              ValueEnumeration enumSet = ((Enumerable)inVal).elements();
              IValue elem;
              if (isTuple) {
                while ((elem = enumSet.nextElement()) != null) {
                  Context c1 = c;
                  IValue[] tuple = ((TupleValue)elem).elems;
                  for (int i = 0; i < bvars.length; i++) {
                    c1 = c1.cons(bvars[i], tuple[i]);
                  }
                  IValue bval = this.eval(pred, c1, s0, s1, control, cm);
                  if (!(bval instanceof BoolValue)) {
                    Assert.fail("Attempted to evaluate an expression of form {x \\in S : P(x)}" +
                                " when P was " + bval.getKindString() + ".\n" + pred);
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
                  IValue bval = this.eval(pred, c1, s0, s1, control, cm);
                  if (!(bval instanceof BoolValue)) {
                    Assert.fail("Attempted to evaluate an expression of form {x \\in S : P(x)}" +
                                " when P was " + bval.getKindString() + ".\n" + pred);
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
            IValue[] vals = new IValue[alen];
            for (int i = 0; i < alen; i++) {
              vals[i] = this.eval(args[i], c, s0, s1, control, cm);
            }
            return setSource(expr, new TupleValue(vals, cm));
          }
        case OPCODE_uc:     // UnboundedChoose
          {
            Assert.fail("TLC attempted to evaluate an unbounded CHOOSE.\n" +
                        "Make sure that the expression is of form CHOOSE x \\in S: P(x).\n" +
                        expr);
            return null;    // make compiler happy
          }
        case OPCODE_ue:     // UnboundedExists
          {
            Assert.fail("TLC attempted to evaluate an unbounded \\E.\n" +
                        "Make sure that the expression is of form \\E x \\in S: P(x).\n" +
                        expr);
            return null;    // make compiler happy
          }
        case OPCODE_uf:     // UnboundedForall
          {
            Assert.fail("TLC attempted to evaluate an unbounded \\A.\n" +
                        "Make sure that the expression is of form \\A x \\in S: P(x).\n" +
                        expr);
            return null;    // make compiler happy
          }
        case OPCODE_lnot:
          {
            IValue arg = this.eval(args[0], c, s0, s1, control, cm);
            if (!(arg instanceof BoolValue)) {
              Assert.fail("Attempted to apply the operator ~ to a non-boolean\n(" +
                          arg.getKindString() + ")\n" + expr);
            }
            return (((BoolValue)arg).val) ? ValFalse : ValTrue;
          }
        case OPCODE_subset:
          {
            IValue arg = this.eval(args[0], c, s0, s1, control, cm);
			return setSource(expr, new SubsetValue(arg, cm));
          }
        case OPCODE_union:
          {
            IValue arg = this.eval(args[0], c, s0, s1, control, cm);
            return setSource(expr, UnionValue.union(arg));
          }
        case OPCODE_domain:
          {
            IValue arg = this.eval(args[0], c, s0, s1, control, cm);
            if (!(arg instanceof Applicable)) {
              Assert.fail("Attempted to apply the operator DOMAIN to a non-function\n(" +
                          arg.getKindString() + ")\n" + expr);
            }
            return setSource(expr, ((Applicable)arg).getDomain());
          }
        case OPCODE_enabled:
          {
            TLCState sfun = TLCStateFun.Empty;
            Context c1 = Context.branch(c);
            sfun = this.enabled(args[0], ActionItemList.Empty, c1, s0, sfun, cm);
            return (sfun != null) ? ValTrue : ValFalse;
          }
        case OPCODE_eq:
          {
            IValue arg1 = this.eval(args[0], c, s0, s1, control, cm);
            IValue arg2 = this.eval(args[1], c, s0, s1, control, cm);
            return (arg1.equals(arg2)) ? ValTrue : ValFalse;
          }
        case OPCODE_land:
          {
            IValue arg1 = this.eval(args[0], c, s0, s1, control, cm);
            if (!(arg1 instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form P /\\ Q" +
                          " when P was\n" + arg1.getKindString() + ".\n" + expr);
            }
            if (((BoolValue)arg1).val) {
              IValue arg2 = this.eval(args[1], c, s0, s1, control, cm);
              if (!(arg2 instanceof BoolValue)) {
                Assert.fail("Attempted to evaluate an expression of form P /\\ Q" +
                            " when Q was\n" + arg2.getKindString() + ".\n" + expr);
              }
              return arg2;
            }
            return ValFalse;
          }
        case OPCODE_lor:
          {
            IValue arg1 = this.eval(args[0], c, s0, s1, control, cm);
            if (!(arg1 instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form P \\/ Q" +
                          " when P was\n" + arg1.getKindString() + ".\n" + expr);
            }
            if (((BoolValue)arg1).val) {
              return ValTrue;
            }
            IValue arg2 = this.eval(args[1], c, s0, s1, control, cm);
            if (!(arg2 instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form P \\/ Q" +
                          " when Q was\n" + arg2.getKindString() + ".\n" + expr);
            }
            return arg2;
          }
        case OPCODE_implies:
          {
            IValue arg1 = this.eval(args[0], c, s0, s1, control, cm);
            if (!(arg1 instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form P => Q" +
                          " when P was\n" + arg1.getKindString() + ".\n" + expr);
            }
            if (((BoolValue)arg1).val) {
              IValue arg2 = this.eval(args[1], c, s0, s1, control, cm);
              if (!(arg2 instanceof BoolValue)) {
                Assert.fail("Attempted to evaluate an expression of form P => Q" +
                            " when Q was\n" + arg2.getKindString() + ".\n" + expr);
              }
              return arg2;
            }
            return ValTrue;
          }
        case OPCODE_equiv:
          {
            IValue arg1 = this.eval(args[0], c, s0, s1, control, cm);
            IValue arg2 = this.eval(args[1], c, s0, s1, control, cm);
            if (!(arg1 instanceof BoolValue) || !(arg2 instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form P <=> Q" +
                          " when P or Q was not a boolean.\n" + expr);
            }
            BoolValue bval1 = (BoolValue)arg1;
            BoolValue bval2 = (BoolValue)arg2;
            return (bval1.val == bval2.val) ? ValTrue : ValFalse;
          }
        case OPCODE_noteq:
          {
            IValue arg1 = this.eval(args[0], c, s0, s1, control, cm);
            IValue arg2 = this.eval(args[1], c, s0, s1, control, cm);
            return arg1.equals(arg2) ? ValFalse : ValTrue;
          }
        case OPCODE_subseteq:
          {
            IValue arg1 = this.eval(args[0], c, s0, s1, control, cm);
            IValue arg2 = this.eval(args[1], c, s0, s1, control, cm);
            if (!(arg1 instanceof Enumerable)) {
              Assert.fail("Attempted to evaluate an expression of form S \\subseteq T," +
                          " but S was not enumerable.\n" + expr);
            }
            return ((Enumerable) arg1).isSubsetEq(arg2);
          }
        case OPCODE_in:
          {
            IValue arg1 = this.eval(args[0], c, s0, s1, control, cm);
            IValue arg2 = this.eval(args[1], c, s0, s1, control, cm);
            return (arg2.member(arg1)) ? ValTrue : ValFalse;
          }
        case OPCODE_notin:
          {
            IValue arg1 = this.eval(args[0], c, s0, s1, control, cm);
            IValue arg2 = this.eval(args[1], c, s0, s1, control, cm);
            return (arg2.member(arg1)) ? ValFalse : ValTrue;
          }
        case OPCODE_setdiff:
          {
            IValue arg1 = this.eval(args[0], c, s0, s1, control, cm);
            IValue arg2 = this.eval(args[1], c, s0, s1, control, cm);
            if (arg1 instanceof Reducible) {
              return setSource(expr, ((Reducible)arg1).diff(arg2));
            }
            return setSource(expr, new SetDiffValue(arg1, arg2));
          }
        case OPCODE_cap:
          {
            IValue arg1 = this.eval(args[0], c, s0, s1, control, cm);
            IValue arg2 = this.eval(args[1], c, s0, s1, control, cm);
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
            IValue arg1 = this.eval(args[0], c, s0, s1, control, cm);
            IValue arg2 = this.eval(args[1], c, s0, s1, control, cm);
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
            return this.eval(args[0], c, s1, null, EvalControl.setPrimedIfEnabled(control), cm);
          }
        case OPCODE_unchanged:
          {
            IValue v0 = this.eval(args[0], c, s0, TLCState.Empty, control, cm);
            IValue v1 = this.eval(args[0], c, s1, null, EvalControl.setPrimedIfEnabled(control), cm);
            return (v0.equals(v1)) ? ValTrue : ValFalse;
          }
        case OPCODE_aa:     // <A>_e
          {
            IValue res = this.eval(args[0], c, s0, s1, control, cm);
            if (!(res instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form <A>_e," +
                          " but A was not a boolean.\n" + expr);
            }
            if (!((BoolValue)res).val) {
              return ValFalse;
            }
            IValue v0 = this.eval(args[1], c, s0, TLCState.Empty, control, cm);
            IValue v1 = this.eval(args[1], c, s1, null, EvalControl.setPrimedIfEnabled(control), cm);
            return v0.equals(v1) ? ValFalse : ValTrue;
          }
        case OPCODE_sa:     // [A]_e
          {
            IValue res = this.eval(args[0], c, s0, s1, control, cm);
            if (!(res instanceof BoolValue)) {
              Assert.fail("Attempted to evaluate an expression of form [A]_e," +
                          " but A was not a boolean.\n" + expr);
            }
            if (((BoolValue)res).val) {
              return ValTrue;
            }
            IValue v0 = this.eval(args[1], c, s0, TLCState.Empty, control, cm);
            IValue v1 = this.eval(args[1], c, s1, null, EvalControl.setPrimedIfEnabled(control), cm);
            return (v0.equals(v1)) ? ValTrue : ValFalse;
          }
        case OPCODE_cdot:
          {
            Assert.fail("The current version of TLC does not support action composition.");
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
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"SF", expr.toString()});
            return null;    // make compiler happy
          }
        case OPCODE_wf:     // WF
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"WF", expr.toString()});
            return null;    // make compiler happy
          }
        case OPCODE_te:     // TemporalExists
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"\\EE", expr.toString()});
            return null;    // make compiler happy
          }
        case OPCODE_tf:     // TemporalForAll
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"\\AA", expr.toString()});
            return null;    // make compiler happy
          }
        case OPCODE_leadto:
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"a ~> b", expr.toString()});
            return null;    // make compiler happy
          }
        case OPCODE_arrow:
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"a -+-> formula", expr.toString()});
            return null;    // make compiler happy
          }
        case OPCODE_box:
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"[]A", expr.toString()});
            return null;    // make compiler happy
          }
        case OPCODE_diamond:
          {
            Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"<>A", expr.toString()});
            return null;    // make compiler happy
          }

        default:
          {
            Assert.fail("TLC BUG: could not evaluate this expression.\n" + expr);
            return null;
          }
        }
  }

  private final IValue setSource(final SemanticNode expr, final IValue value) {
    if (this.callStack != null) {
      value.setSource(expr);
    }
    return value;
  }

  /**
   * This method determines if the argument is a valid state.  A state
   * is good iff it assigns legal explicit values to all the global
   * state variables.
   */
  public final boolean isGoodState(TLCState state) {
    return state.allAssigned();
  }

  /* This method determines if a state satisfies the model constraints. */
  public final boolean isInModel(TLCState state) throws EvalException {
    ExprNode[] constrs = this.getModelConstraints();
    for (int i = 0; i < constrs.length; i++) {
      IValue bval = this.eval(constrs[i], Context.Empty, state, CostModel.DO_NOT_RECORD);
      if (!(bval instanceof BoolValue)) {
        Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", constrs[i].toString()});
      }
      if (!((BoolValue)bval).val) return false;
    }
    return true;
  }

  /* This method determines if a pair of states satisfy the action constraints. */
  public final boolean isInActions(TLCState s1, TLCState s2) throws EvalException {
    ExprNode[] constrs = this.getActionConstraints();
    for (int i = 0; i < constrs.length; i++) {
      IValue bval = this.eval(constrs[i], Context.Empty, s1, s2, EvalControl.Clear, CostModel.DO_NOT_RECORD);
      if (!(bval instanceof BoolValue)) {
        Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", constrs[i].toString()});
      }
      if (!((BoolValue)bval).val) return false;
    }
    return true;
  }

  /**
   * This method determines if an action is enabled in the given state.
   * More precisely, it determines if (act.pred /\ (sub' # sub)) is
   * enabled in the state s and context act.con.
 * @param cm TODO
   */
  public final TLCState enabled(SemanticNode pred, ActionItemList acts,
                                Context c, TLCState s0, TLCState s1, CostModel cm) {
	    if (this.callStack != null) {
	    	return enabledWithCallStack(pred, acts, c, s0, s1, cm);
	    } else {
	    	return enabledImpl(pred, acts, c, s0, s1, cm);
	    }
  }

  private final TLCState enabledWithCallStack(SemanticNode pred, ActionItemList acts,
          Context c, TLCState s0, TLCState s1, CostModel cm) {
    this.callStack.push(pred);
    try {
    	return enabledImpl(pred, acts, c, s0, s1, cm);
    } catch (TLCRuntimeException | EvalException e) {
    	// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context, TLCState, IStateFunctor)
    	this.callStack.freeze();
    	throw e;
    } finally {
    	this.callStack.pop();
    }
  }
  
  private final TLCState enabledImpl(SemanticNode pred, ActionItemList acts,
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
                IValue rhs = new LazyValue(opDef.getBody(), c1, cm);
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
              c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, coverage ? sub.getCM() : cm));
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
              c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, cm));
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
            Assert.fail("Attempted to compute ENABLED on a non-boolean expression.\n" + pred);
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
    if (kind > ActionItemList.CONJUNCT) {
      TLCState res = this.enabled(pred, acts1, c, s0, s1, cm);
      return res;
    }
    else if (kind == ActionItemList.PRED) {
      TLCState res = this.enabled(pred, acts1, c, s0, s1, cm);
      return res;
    }
    if (kind == ActionItemList.UNCHANGED) {
      TLCState res = this.enabledUnchanged(pred, acts1, c, s0, s1, cm);
      return res;
    }

    IValue v1 = this.eval(pred, c, s0, TLCState.Empty, EvalControl.Enabled, cm);
	// We are now in ENABLED and primed state. Second TLCState parameter being null
	// effectively disables LazyValue in evalAppl (same effect as
	// EvalControl.setPrimed(EvalControl.Enabled)).
    IValue v2 = this.eval(pred, c, s1, null, EvalControl.Primed, cm);

    if (v1.equals(v2)) return null;
    TLCState res = this.enabled(acts1, s0, s1, cm);
    return res;
  }

  private final TLCState enabledAppl(OpApplNode pred, ActionItemList acts, Context c, TLCState s0, TLCState s1, CostModel cm)
  {
	    if (this.callStack != null) {
	    	return enabledApplWithCallStack(pred, acts, c, s0, s1, cm);
	    } else {
	    	return enabledApplImpl(pred, acts, c, s0, s1, cm);
	    }
  }

  private final TLCState enabledApplWithCallStack(OpApplNode pred, ActionItemList acts, Context c, TLCState s0, TLCState s1, CostModel cm)
  {
	    this.callStack.push(pred);
	    try {
	    	return enabledApplImpl(pred, acts, c, s0, s1, cm);
	    } catch (TLCRuntimeException | EvalException e) {
	    	// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context, TLCState, IStateFunctor)
	    	this.callStack.freeze();
	    	throw e;
	    } finally {
	    	this.callStack.pop();
	    }
  }
 
  private final TLCState enabledApplImpl(OpApplNode pred, ActionItemList acts, Context c, TLCState s0, TLCState s1, CostModel cm)
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
              Context c1 = this.getOpContext(opDef, args, c, true, cm);
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
            }
          } else
          {
            if (val instanceof OpValue)
            {
              Applicable op = (Applicable) val;
              IValue[] argVals = new IValue[alen];
              // evaluate the actuals:
              for (int i = 0; i < alen; i++)
              {
                argVals[i] = this.eval(args[i], c, s0, s1, EvalControl.Enabled, cm);
              }
              // apply the operator:
              bval = op.apply(argVals, EvalControl.Enabled);
            }
          }

          if (opcode == 0)
          {
            if (!(bval instanceof BoolValue))
            {
              Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[] { "ENABLED", "boolean",
                      bval.toString(), pred.toString() });
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
            ActionItemList acts1 = acts.cons(args[1], c, cm, ActionItemList.CHANGED);
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
              acts1 = acts1.cons(body, c2, cm, ActionItemList.PRED);
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
                IValue bval = this.eval(pairArgs[0], c, s0, s1, EvalControl.Enabled, cm);
                if (!(bval instanceof BoolValue))
                {
                  Assert.fail("In computing ENABLED, a non-boolean expression(" + bval.getKindString()
                          + ") was used as a guard condition" + " of a CASE.\n" + pairArgs[1]);
                }
                if (((BoolValue) bval).val)
                {
                  return this.enabled(pairArgs[1], acts, c, s0, s1, cm);
                }
              }
            }
            if (other == null)
            {
              Assert.fail("In computing ENABLED, TLC encountered a CASE with no" + " conditions true.\n" + pred);
            }
            return this.enabled(other, acts, c, s0, s1, cm);
          }
        case OPCODE_cl: // ConjList
        case OPCODE_land:
          {
            ActionItemList acts1 = acts;
            for (int i = alen - 1; i > 0; i--)
            {
              acts1 = acts1.cons(args[i], c, cm, i);
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
            IValue fval = this.eval(args[0], c, s0, s1, EvalControl.setKeepLazy(EvalControl.Enabled), cm); // KeepLazy does not interfere with EvalControl.Enabled in this.evalAppl
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
              IValue argVal = this.eval(args[1], c, s0, s1, EvalControl.Enabled, cm);
              IValue bval = fcn.apply(argVal, EvalControl.Enabled); // EvalControl.Enabled not taken into account by any subclass of Applicable
              if (!(bval instanceof BoolValue))
              {
                Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING2, new String[] { "ENABLED", "boolean",
                        pred.toString() });
              }
              if (!((BoolValue) bval).val) {
                return null;
              }
            } else
            {
              Assert.fail("In computing ENABLED, a non-function (" + fval.getKindString()
                      + ") was applied as a function.\n" + pred);
            }
            return this.enabled(acts, s0, s1, cm);
          }
        case OPCODE_ite: // IfThenElse
          {
            IValue guard = this.eval(args[0], c, s0, s1, EvalControl.Enabled, cm);
            if (!(guard instanceof BoolValue))
            {
              Assert.fail("In computing ENABLED, a non-boolean expression(" + guard.getKindString()
                      + ") was used as the guard condition" + " of an IF.\n" + pred);
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
            Assert.fail("In computing ENABLED, TLC encountered temporal quantifier.\n" + pred);
            return null; // make compiler happy
          }
        case OPCODE_uc: // UnboundedChoose
          {
            Assert.fail("In computing ENABLED, TLC encountered unbounded CHOOSE. "
                    + "Make sure that the expression is of form CHOOSE x \\in S: P(x).\n" + pred);
            return null; // make compiler happy
          }
        case OPCODE_ue: // UnboundedExists
          {
            Assert.fail("In computing ENABLED, TLC encountered unbounded quantifier. "
                    + "Make sure that the expression is of form \\E x \\in S: P(x).\n" + pred);
            return null; // make compiler happy
          }
        case OPCODE_uf: // UnboundedForall
          {
            Assert.fail("In computing ENABLED, TLC encountered unbounded quantifier. "
                    + "Make sure that the expression is of form \\A x \\in S: P(x).\n" + pred);
            return null; // make compiler happy
          }
        case OPCODE_sf: // SF
          {
            Assert.fail(EC.TLC_ENABLED_WRONG_FORMULA, new String[]{ "SF", pred.toString()});
            return null; // make compiler happy
          }
        case OPCODE_wf: // WF
          {
            Assert.fail(EC.TLC_ENABLED_WRONG_FORMULA, new String[] { "WF", pred.toString() });
            return null; // make compiler happy
          }
        case OPCODE_box:
          {
            Assert.fail(EC.TLC_ENABLED_WRONG_FORMULA, new String[] { "[]", pred.toString() });
            return null; // make compiler happy
          }
        case OPCODE_diamond:
          {
            Assert.fail(EC.TLC_ENABLED_WRONG_FORMULA, new String[] { "<>", pred.toString() });
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
              IValue bval = this.eval(pred, c, s0, s1, EvalControl.Enabled, cm);
              if (!((BoolValue) bval).val) {
                return null;
              }
            } else
            {
              UniqueString varName = var.getName();
              IValue lval = s1.lookup(varName);
              IValue rval = this.eval(args[1], c, s0, s1, EvalControl.Enabled, cm);
              if (lval == null)
              {
                TLCState s2 = s1.bind(var, rval, pred);
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
            IValue bval = this.eval(args[0], c, s0, s1, EvalControl.Enabled, cm);
            if (!(bval instanceof BoolValue))
            {
              Assert.fail("While computing ENABLED of an expression of the form" + " P => Q, P was "
                      + bval.getKindString() + ".\n" + pred);
            }
            if (((BoolValue) bval).val)
            {
              return this.enabled(args[1], acts, c, s0, s1, cm);
            }
            return this.enabled(acts, s0, s1, cm);
          }
        case OPCODE_cdot:
          {
            Assert.fail("The current version of TLC does not support action composition.");
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
            Assert.fail("In computing ENABLED, TLC encountered a temporal formula" + " (a ~> b).\n" + pred);
            return null; // make compiler happy
          }
        case OPCODE_arrow:
          {
            Assert.fail("In computing ENABLED, TLC encountered a temporal formula" + " (a -+-> formula).\n" + pred);
            return null; // make compiler happy
          }
        case OPCODE_in:
          {
            SymbolNode var = this.getPrimedVar(args[0], c, true);
            if (var == null)
            {
                IValue bval = this.eval(pred, c, s0, s1, EvalControl.Enabled, cm);
                if (!((BoolValue) bval).val) {
                  return null;
                }
            } else
            {
              UniqueString varName = var.getName();
              IValue lval = s1.lookup(varName);
              IValue rval = this.eval(args[1], c, s0, s1, EvalControl.Enabled, cm);
              if (lval == null)
              {
                if (!(rval instanceof Enumerable))
                {
                  Assert.fail("The right side of \\IN is not enumerable.\n" + pred);
                }
                ValueEnumeration Enum = ((Enumerable) rval).elements();
                IValue val;
                while ((val = Enum.nextElement()) != null)
                {
                  TLCState s2 = s1.bind(var, val, pred);
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
            IValue bval = this.eval(pred, c, s0, s1, EvalControl.Enabled, cm);
            if (!(bval instanceof BoolValue))
            {
              Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[] { "ENABLED", "boolean",
                      bval.toString(), pred.toString() });
            }
            if (((BoolValue) bval).val)
            {
              return this.enabled(acts, s0, s1, cm);
            }
            return null;
          }
        }
  }

  private final TLCState enabledUnchanged(SemanticNode expr, ActionItemList acts,
                                          Context c, TLCState s0, TLCState s1, CostModel cm) {
	    if (this.callStack != null) {
	    	return enabledUnchangedWithCallStack(expr, acts, c, s0, s1, cm);
	    } else {
	    	return enabledUnchangedImpl(expr, acts, c, s0, s1, cm);
	    }
  }

  private final TLCState enabledUnchangedWithCallStack(SemanticNode expr, ActionItemList acts,
          Context c, TLCState s0, TLCState s1, CostModel cm) {
    this.callStack.push(expr);
    try {
    	return enabledUnchangedImpl(expr, acts, c, s0, s1, cm);
    } catch (TLCRuntimeException | EvalException e) {
    	// see tlc2.tool.Tool.getInitStates(SemanticNode, ActionItemList, Context, TLCState, IStateFunctor)
    	this.callStack.freeze();
    	throw e;
    } finally {
    	this.callStack.pop();
    }
  }
  
  private final TLCState enabledUnchangedImpl(SemanticNode expr, ActionItemList acts,
            Context c, TLCState s0, TLCState s1, CostModel cm) {
        SymbolNode var = this.getVar(expr, c, true);
        if (var != null) {
          // a state variable, e.g. UNCHANGED var1
          UniqueString varName = var.getName();
          IValue v0 = this.eval(expr, c, s0, s1, EvalControl.Enabled, cm);
          IValue v1 = s1.lookup(varName);
          if (v1 == null) {
            s1 = s1.bind(var, v0, expr);
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
                acts1 = acts1.cons(args[i], c, cm, ActionItemList.UNCHANGED);
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
                          opName + " in an UNCHANGED expression at\n" + expr);
            }
            return this.enabled(acts, s0, s1, cm);
          }
        }

        final IValue v0 = this.eval(expr, c, s0, TLCState.Empty, EvalControl.Enabled, cm);
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
		final IValue v1 = this.eval(expr, c, s1, TLCState.Empty, EvalControl.Primed, cm);
        if (!v0.equals(v1)) {
          return null;
        }
        return this.enabled(acts, s0, s1, cm);
  }

  /* This method determines if the action predicate is valid in (s0, s1). */
  public final boolean isValid(Action act, TLCState s0, TLCState s1) {
    IValue val = this.eval(act.pred, act.con, s0, s1, EvalControl.Clear, act.cm);
    if (!(val instanceof BoolValue)) {
      Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", act.pred.toString()});
    }
    return ((BoolValue)val).val;
  }

  /* Returns true iff the predicate is valid in the state. */
  public final boolean isValid(Action act, TLCState state) {
    return this.isValid(act, state, TLCState.Empty);
  }

  /* Returns true iff the predicate is valid in the state. */
  public final boolean isValid(Action act) {
    return this.isValid(act, TLCState.Empty, TLCState.Empty);
  }

  public final boolean isValid(ExprNode expr) {
    IValue val = this.eval(expr, Context.Empty, TLCState.Empty, CostModel.DO_NOT_RECORD);
    if (!(val instanceof BoolValue)) {
      Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()});
    }
    return ((BoolValue)val).val;
  }

    /* Reconstruct the initial state whose fingerprint is fp. */
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
		if (functor.state != null) {
			final String info = "<Initial predicate>";
			final TLCStateInfo tlcStateInfo = new TLCStateInfo(functor.state, info, 1, fp);
			return tlcStateInfo;
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
  public final TLCStateInfo getState(long fp, TLCState s) {
	  IdThread.setCurrentState(s);
    for (int i = 0; i < this.actions.length; i++) {
      Action curAction = this.actions[i];
      StateVec nextStates = this.getNextStates(curAction, s);
      for (int j = 0; j < nextStates.size(); j++) {
        TLCState state = nextStates.elementAt(j);
        long nfp = state.fingerPrint();
        if (fp == nfp) {
          return new TLCStateInfo(state, curAction.getLocation());
        }
      }
    }
    return null;
  }

  /* Reconstruct the info for s1.   */
  public final TLCStateInfo getState(TLCState s1, TLCState s) {
	  IdThread.setCurrentState(s);
    for (int i = 0; i < this.actions.length; i++) {
      Action curAction = this.actions[i];
      StateVec nextStates = this.getNextStates(curAction, s);
      for (int j = 0; j < nextStates.size(); j++) {
        TLCState state = nextStates.elementAt(j);
        if (s1.equals(state)) {
          return new TLCStateInfo(state, curAction.getLocation());
        }
      }
    }
    return null;
  }

  /* Return the set of all permutations under the symmetry assumption. */
  public final MVPerm[] getSymmetryPerms() {
    final String name = this.config.getSymmetry();
    if (name.length() == 0) { return null; }
    final Object symm = this.defns.get(name);
    if (symm == null) {
      Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "symmetry function", name});
    }
    if (!(symm instanceof OpDefNode)) {
      Assert.fail("The symmetry function " + name + " must specify a set of permutations.");
    }
    // This calls tlc2.module.TLC.Permutations(Value) and returns a Value of |fcns|
    // = n! where n is the capacity of the symmetry set.
    final IValue fcns = this.eval(((OpDefNode)symm).getBody(), Context.Empty, TLCState.Empty, CostModel.DO_NOT_RECORD);
    if (!(fcns instanceof Enumerable)) {
      Assert.fail("The symmetry operator must specify a set of functions.");
    }
    return MVPerm.permutationSubgroup((Enumerable) fcns);
  }

  public final boolean hasSymmetry() {
    if (this.config == null) {
      return false;
    }
    final String name = this.config.getSymmetry();
    return name.length() > 0;
  }
  public final Context getFcnContext(FcnLambdaValue fcn, ExprOrOpArgNode[] args,
          Context c, TLCState s0, TLCState s1,
          final int control) {
	  return getFcnContext(fcn, args, c, s0, s1, control, CostModel.DO_NOT_RECORD);
  }

  public final Context getFcnContext(FcnLambdaValue fcn, ExprOrOpArgNode[] args,
                                     Context c, TLCState s0, TLCState s1,
                                     final int control, CostModel cm) {
    Context fcon = fcn.con;
    int plen = fcn.params.length();
    FormalParamNode[][] formals = fcn.params.formals;
    IValue[] domains = fcn.params.domains;
    boolean[] isTuples = fcn.params.isTuples;
    IValue argVal = this.eval(args[1], c, s0, s1, control, cm);

    if (plen == 1) {
      if (!domains[0].member(argVal)) {
        Assert.fail("In applying the function\n" + Values.ppr(fcn.toString()) +
                    ",\nthe first argument is:\n" + Values.ppr(argVal.toString()) +
                    "which is not in its domain.\n" + args[0]);
      }
      if (isTuples[0]) {
        FormalParamNode[] ids = formals[0];
        TupleValue tv = (TupleValue) argVal.toTuple();
        if (tv == null || argVal.size() != ids.length) {
          Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                      ",\nthe argument is:\n" + Values.ppr(argVal.toString()) +
                      "which does not match its formal parameter.\n" + args[0]);
        }
        IValue[] elems = tv.elems;
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
                    " domain.\n" + args[0]);
      }
      int argn = 0;
      IValue[] elems = tv.elems;
      for (int i = 0; i < formals.length; i++) {
        FormalParamNode[] ids = formals[i];
        IValue domain = domains[i];
        if (isTuples[i]) {
          if (!domain.member(elems[argn])) {
            Assert.fail("In applying the function\n" + Values.ppr(fcn.toString()) +
                        ",\nthe argument number " + (argn+1) + " is:\n" +
                        Values.ppr(elems[argn].toString()) +
                        "\nwhich is not in its domain.\n" + args[0]);
          }
          TupleValue tv1 = (TupleValue) elems[argn++].toTuple();
          if (tv1 == null || tv1.size() != ids.length) {
            Assert.fail("In applying the function\n" + Values.ppr(fcn.toString()) +
                        ",\nthe argument number " + argn + " is:\n" +
                        Values.ppr(elems[argn-1].toString()) +
                        "which does not match its formal parameter.\n" + args[0]);
          }
          IValue[] avals = tv1.elems;
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
                          "which is not in its domain.\n" + args[0]);
            }
            fcon = fcon.cons(ids[j], elems[argn++]);
          }
        }
      }
    }
    return fcon;
  }

  public final ContextEnumerator contexts(OpApplNode appl, Context c, TLCState s0,
          TLCState s1, final int control) {
	  return contexts(appl, c, s0, s1, control, CostModel.DO_NOT_RECORD);
  }
  
  /* A context enumerator for an operator application. */
  public final ContextEnumerator contexts(OpApplNode appl, Context c, TLCState s0,
                                          TLCState s1, final int control, CostModel cm) {
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
      IValue boundSet = this.eval(domains[i], c, s0, s1, control, cm);
      if (!(boundSet instanceof Enumerable)) {
        Assert.fail("TLC encountered a non-enumerable quantifier bound\n" +
                    Values.ppr(boundSet.toString()) + ".\n" + domains[i]);
      }
      FormalParamNode[] farg = formals[i];
      if (isTuples[i]) {
        vars[idx] = farg;
        enums[idx++] = ((Enumerable)boundSet).elements();
      }
      else {
        for (int j = 0; j < farg.length; j++) {
          vars[idx] = farg[j];
          enums[idx++] = ((Enumerable)boundSet).elements();
        }
      }
    }
    return new ContextEnumerator(vars, enums, c);
  }

  /**
   * This method converts every definition that is constant into TLC
   * value. By doing this, TLC avoids evaluating the same expression
   * multiple times.
   *
   * The method runs for every module in the module tables.
   *
   * Modified by LL on 23 July 2013 so it is not run for modules that are
   * instantiated and have parameters (CONSTANT or VARIABLE declarations)
   */
  private void processConstantDefns() {
      ModuleNode[] mods = this.moduleTbl.getModuleNodes();
      for (int i = 0; i < mods.length; i++) {
        if (   (! mods[i].isInstantiated())
          || (   (mods[i].getConstantDecls().length == 0)
            && (mods[i].getVariableDecls().length == 0) ) ) {
            this.processConstantDefns(mods[i]);
        }
      }
  }

  /**
   * Converts the constant definitions in the corresponding value for the
   * module -- that is, it "converts" (which seems to mean calling deepNormalize)
   * the values substituted for the declared constants.  On 17 Mar 2012 it was
   * modified by LL to evaluate the OpDefNode when a defined operator is substituted
   * for an ordinary declared constant (not a declared operator constant).  Without this
   * evaluation, the definition gets re-evaluated every time TLC evaluates the declared
   * constant.  LL also added a check that an operator substituted for the declared
   * constant also has the correct arity.
   *
   * @param mod the module to run on
   */
  private void processConstantDefns(ModuleNode mod) {

    // run for constant definitions
    OpDeclNode[] consts = mod.getConstantDecls();
    for (int i = 0; i < consts.length; i++) {
      Object val = consts[i].getToolObject(TLCGlobals.ToolId);
      if (val != null && val instanceof IValue) {
        ((IValue)val).deepNormalize();
        // System.err.println(consts[i].getName() + ": " + val);
      } // The following else clause was added by LL on 17 March 2012.
      else if (val != null && val instanceof OpDefNode) {
        OpDefNode opDef = (OpDefNode) val;
        // The following check logically belongs in Spec.processSpec, but it's not there.
        // So, LL just added it here.  This error cannot occur when running TLC from
        // the Toolbox.
        Assert.check(opDef.getArity() == consts[i].getArity(),
                     EC.TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS,
                     new String[] {consts[i].getName().toString(), opDef.getName().toString()});

        if (opDef.getArity() == 0) {
          try {
            IValue defVal = this.eval(opDef.getBody(), Context.Empty, TLCState.Empty, CostModel.DO_NOT_RECORD);
            defVal.deepNormalize();
            consts[i].setToolObject(TLCGlobals.ToolId, defVal);
          } catch (Assert.TLCRuntimeException e) {
            Assert.fail(EC.TLC_CONFIG_SUBSTITUTION_NON_CONSTANT,
                new String[] { consts[i].getName().toString(), opDef.getName().toString() });
          }
        }
      }
    }

    // run for constant operator definitions
    OpDefNode[] opDefs = mod.getOpDefs();
    for (int i = 0; i < opDefs.length; i++) {
      OpDefNode opDef = opDefs[i];

      // The following variable evaluate and its value added by LL on 24 July 2013
      // to prevent pre-evaluation of a definition from an EXTENDS of a module that
      // is also instantiated.
      ModuleNode moduleNode = opDef.getOriginallyDefinedInModuleNode() ;
      boolean evaluate =    (moduleNode == null)
                     || (! moduleNode.isInstantiated())
                     || (   (moduleNode.getConstantDecls().length == 0)
                         && (moduleNode.getVariableDecls().length == 0) ) ;

      if (evaluate && opDef.getArity() == 0) {
        Object realDef = this.lookup(opDef, Context.Empty, false);
        if (realDef instanceof OpDefNode) {
          opDef = (OpDefNode)realDef;
          if (this.getLevelBound(opDef.getBody(), Context.Empty) == 0) {
            try {
              UniqueString opName = opDef.getName();
              // System.err.println(opName);
              IValue val = this.eval(opDef.getBody(), Context.Empty, TLCState.Empty, CostModel.DO_NOT_RECORD);
              val.deepNormalize();
              // System.err.println(opName + ": " + val);
              opDef.setToolObject(TLCGlobals.ToolId, val);
              Object def = this.defns.get(opName);
              if (def == opDef) {
                this.defns.put(opName, val);
              }
            }
            catch (Throwable e) {
              // Assert.printStack(e);
            }
          }
        }
      }
    }

    // run for all inner modules
    ModuleNode[] imods = mod.getInnerModules();
    for (int i = 0; i < imods.length; i++) {
      this.processConstantDefns(imods[i]);
    }
  }

}
