// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 19 May 2008 at  1:13:48 PST by lamport
//      modified on Fri Aug 24 14:43:24 PDT 2001 by yuanyu

package tlc2.tool.impl;

import java.io.File;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import tla2sany.modanalyzer.ParseUnit;
import tla2sany.semantic.APSubstInNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.FrontEnd;
import tla2sany.semantic.LabelNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.tool.Action;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.Defns;
import tlc2.tool.TLCState;
import tlc2.tool.ToolGlobals;
import tlc2.util.Context;
import tlc2.util.ObjLongTable;
import tlc2.util.Vect;
import tlc2.value.ValueConstants;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.ModelValue;
import util.Assert;
import util.FilenameToStream;
import util.TLAConstants;
import util.UniqueString;

// Note that we use all of the {@code default} defined functionality in our
//		implemented interface {@link SymbolNodeValueLookupProvider} (and our
//		lack of implementation of {@link OpDefEvaluator} is why this class
//		is marked {@code abstract}.)
abstract class Spec
		implements ValueConstants, ToolGlobals, Serializable, OpDefEvaluator, SymbolNodeValueLookupProvider {
	private static final long serialVersionUID = 1L;

	/**
	 * @see See note on performance in CostModelCreator.
	 */
	protected static final boolean coverage = TLCGlobals.isCoverageEnabled();

	protected static final int toolId = FrontEnd.getToolId();
	
	protected final String specDir; // The spec directory.
    protected final String rootFile; // The root file of this spec.
    protected final String configFile; // The model config file.
    protected final Set<OpDefNode> processedDefs ; 
      // The set of OpDefNodes on which processSpec has been called.
      // Added by LL & YY on 25 June 2014 to eliminate infinite
      // loop when a recursively defined operator is used as an
      // operator argument in its own definition.
    protected final Defns defns; // Global definitions reachable from root
	protected final Defns unprocessedDefns;
    protected final TLAClass tlaClass; // TLA built-in classes.
    private final FilenameToStream resolver; // takes care of path to stream resolution

    protected final ModelConfig config; // The model configuration.
    private final SpecProcessor specProcessor;

    // SZ Feb 20, 2009: added support to name resolver, to be able to run outside of the tool
	public Spec(final String specDir, final String specFile, final String configFile, final FilenameToStream resolver) {
        this.specDir = specDir;
        this.rootFile = specFile;
        this.defns = new Defns();
        this.tlaClass = new TLAClass("tlc2.module", resolver);
        this.processedDefs = new HashSet<OpDefNode>();
        this.resolver = resolver;
        
        // SZ Mar 9, 2009: added initialization of the modelValue class
        ModelValue.init();
        this.configFile = configFile;
        this.config = new ModelConfig(configFile + TLAConstants.Files.CONFIG_EXTENSION, resolver);
        this.config.parse();
        ModelValue.setValues(); // called after seeing all model values

        specProcessor = new SpecProcessor(getRootName(), resolver, toolId, defns, config, this, this, tlaClass);
        
        this.unprocessedDefns = specProcessor.getUnprocessedDefns();
    }
    
    protected Spec(final Spec other) {
    	this.specDir = other.specDir;
    	this.rootFile = other.rootFile;
    	this.configFile = other.configFile;
    	this.processedDefs = other.processedDefs;
    	this.defns = other.defns;
    	this.tlaClass = other.tlaClass;
        this.resolver = other.resolver;
        this.unprocessedDefns = other.unprocessedDefns;
    	this.config = other.config;
        this.specProcessor = other.specProcessor;
    }
    
    public ModelConfig getModelConfig() {
    	return config;
    }
    
    public SpecProcessor getSpecProcessor() {
    	return specProcessor;
    }

    /* Return the variable if expr is a primed state variable. Otherwise, null. */
    public final SymbolNode getPrimedVar(SemanticNode expr, Context c, boolean cutoff)
    {
        if (expr instanceof OpApplNode)
        {
            OpApplNode expr1 = (OpApplNode) expr;
            SymbolNode opNode = expr1.getOperator();

            if (BuiltInOPs.getOpCode(opNode.getName()) == OPCODE_prime)
            {
                return this.getVar(expr1.getArgs()[0], c, cutoff, toolId);
            }

            if (opNode.getArity() == 0)
            {
                boolean isVarDecl = (opNode.getKind() == VariableDeclKind);
                Object val = this.lookup(opNode, c, cutoff && isVarDecl, toolId);

                if (val instanceof LazyValue)
                {
                    LazyValue lval = (LazyValue) val;
                    return this.getPrimedVar(lval.expr, lval.con, cutoff);
                }
                if (val instanceof OpDefNode)
                {
                    return this.getPrimedVar(((OpDefNode) val).getBody(), c, cutoff);
                }
            }
        }
        return null;
    }

    /** 
     * Get model constraints.  
     */
	public final ExprNode[] getModelConstraints() {
		return specProcessor.getModelConstraints();
	}

    /**
     * Get action constraints.  
     */
	public final ExprNode[] getActionConstraints() {
		return specProcessor.getActionConstraints();
	}

    /* Get the initial state predicate of the specification.  */
	public final Vect<Action> getInitStateSpec() {
		return specProcessor.getInitPred();
	}

    /* Get the action (next state) predicate of the specification. */
	public final Action getNextStateSpec() {
		return specProcessor.getNextPred();
	}

    /** 
     * Get the view mapping for the specification. 
     */
    public final SemanticNode getViewSpec()
    {
        String name = this.config.getView();
        if (name.length() == 0)
            return null;

        Object view = this.defns.get(name);
        if (view == null)
        {
            Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "view function", name });
        }
        if (!(view instanceof OpDefNode))
        {
            Assert.fail(EC.TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT, new String[] { "view function", name });
        }
        OpDefNode def = (OpDefNode) view;
        if (def.getArity() != 0)
        {
            Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[] { "view function", name });
        }
        return def.getBody();
    }

    /* Get the type declaration for the state variables. */
    public final SemanticNode getTypeSpec()
    {
        String name = this.config.getType();
        if (name.length() == 0)
        {
            Assert.fail(EC.TLC_CONFIG_NO_STATE_TYPE);
        }

        Object type = this.defns.get(name);
        if (type == null)
        {
            Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "type", name });
        }
        if (!(type instanceof OpDefNode))
        {
            Assert.fail(EC.TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT, new String[] { "type", name });
        }
        OpDefNode def = (OpDefNode) type;
        if (def.getArity() != 0)
        {
            Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[] { "type", name });
        }
        return def.getBody();
    }

    /* Get the type declaration for the state variables. */
    public final SemanticNode getTypeConstraintSpec()
    {
        String name = this.config.getTypeConstraint();
        if (name.length() == 0)
        {
            return null;
        }

        Object type = this.defns.get(name);
        if (type == null)
        {
            Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "type constraint", name });
        }
        if (!(type instanceof OpDefNode))
        {
            Assert.fail(EC.TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT, new String[] { "type constraint", name });
        }
        OpDefNode def = (OpDefNode) type;
        if (def.getArity() != 0)
        {
            Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[] { "type constraint", name });

        }
        return def.getBody();
    }

	public final boolean livenessIsTrue() {
		return getImpliedTemporals().length == 0;
	}

    /* Get the fairness condition of the specification.  */
    public final Action[] getTemporals()
    {
        return specProcessor.getTemporal();
    }

    public final String[] getTemporalNames()
    {
        return specProcessor.getTemporalNames();
    }

    /* Get the liveness checks of the specification.  */
	public final Action[] getImpliedTemporals() {
		return specProcessor.getImpliedTemporals();
	}

	public final String[] getImpliedTemporalNames() {
		return specProcessor.getImpliedTemporalNames();
	}

    /* Get the invariants of the specification. */
	public final Action[] getInvariants() {
		return specProcessor.getInvariants();
	}

	public final String[] getInvNames() {
		return specProcessor.getInvariantsNames();
	}

    /* Get the implied-inits of the specification. */
	public final Action[] getImpliedInits() {
		return specProcessor.getImpliedInits();
	}

	public final String[] getImpliedInitNames() {
		return specProcessor.getImpliedInitNames();
	}

    /* Get the implied-actions of the specification. */
	public final Action[] getImpliedActions() {
		return specProcessor.getImpliedActions();
	}

	public final String[] getImpliedActNames() {
		return specProcessor.getImpliedActionNames();
	}

    /* Get the assumptions of the specification. */
	public final ExprNode[] getAssumptions() {
		return specProcessor.getAssumptions();
	}
    
    /* Get the assumptionIsAxiom field */
    public final boolean[] getAssumptionIsAxiom() {
        return specProcessor.getAssumptionIsAxiom();
    }
    
    /**
     * This method gets the value of a symbol from the environment. We
     * look up in the context c, its tool object, and the state s.
     * 
     * It and the lookup method that follows it were modified by LL
     * on 10 April 2011 to fix the following bug.  When a constant definition
     *    Foo == ...
     * is overridden to substitute Bar for Foo, the TLC tool object for
     * the body of Foo's OpDef node is set to the OpDefNode for Bar.
     * When evaluating a use of Foo, the lookup method is apparently
     * supposed to return the OpDefNode for Bar.  (I don't understand
     * how the callers make use of the returned value.) That's what it
     * does for uses of Foo in the module in which Foo is defined.
     * However, if Foo is imported by instantiation with renaming as 
     * X!Foo, then it appears that looking up X!Foo should also return 
     * the OpDefNode for Bar.  If the instantiated module had no
     * parameters, then that's what happened because the body of the
     * OpDefNode for X!Foo is the same (contains a pointer to the
     * same object) as the body of Foo's OpDefNode.  However, that
     * wasn't the case if the instantiated module had parameters,
     * because then X!Foo's OpDefNode consists of a sequence of
     * nested SubstInNode objects, the last of which points to
     * the body of Foo's OpDefNode.  So, LL modified the lookup
     * methods so they follow the sequence of SubstInNode bodies
     * down to the body of Foo's OpDefNode when looking up the result.  
     * (If a SubstInNode has a non-null TLC tool object for a
     * SubstInNode, then it returns that object.  I don't think this 
     * should ever be the case, and if it is, I have no idea what the
     * lookup method should do.)
     * 
     */
    public final Object lookup(SymbolNode opNode, Context c, TLCState s, boolean cutoff)
    {
        Object result = lookup(opNode, c, cutoff, toolId);
        if (result != opNode) {
            return result;
        }

		// CalvinL/LL/MAK 02/2021: Added conditional as part of Github issue #362 Name
		// clash between variable in refined spec and operator in instantiated spec. See
		// releated test in Github362.java.
        if (opNode.getKind() != UserDefinedOpKind) {
			result = s.lookup(opNode.getName());
			if (result != null) {
				return result;
			}
		}

        return opNode;
    }

    public final Object lookup(final SymbolNode opNode)
    {
        return lookup(opNode, Context.Empty, false, toolId);
    }

    /**
     * The following added by LL on 23 October 2012 to fix bug in evaluation of names of theorems and 
     * assumptions imported by parameterized instantiation.
     *  
     * @param opDef
     * @param args
     * @param c
     * @param cachable
     * @return
     */
    public final Context getOpContext(ThmOrAssumpDefNode opDef, ExprOrOpArgNode[] args, Context c, boolean cachable)
    {
        FormalParamNode[] formals = opDef.getParams();
        int alen = args.length;
        Context c1 = c;
        for (int i = 0; i < alen; i++)
        {
            Object aval = this.getVal(args[i], c, cachable, toolId);
            c1 = c1.cons(formals[i], aval);
        }
        return c1;
    }
    
    /**
     * Return a table containing the locations of subexpression in the
     * spec of forms x' = e and x' \in e. Warning: Current implementation
     * may not be able to find all such locations.
     */
    public final ObjLongTable<SemanticNode> getPrimedLocs()
    {
        final ObjLongTable<SemanticNode> tbl = new ObjLongTable<SemanticNode>(10);
        final Action act = this.getNextStateSpec();
		if (act == null) {
			// MAK 10/17/2018: If spec defines no next-state action (see e.g.
			// tlc2.tool.ASTest) and this method is called before ModelChecker checks
			// actions (search for tlc2.output.EC.TLC_STATES_AND_NO_NEXT_ACTION) this will
			// NPE.
			return tbl;
		}
        this.collectPrimedLocs(act.pred, act.con, tbl);
        return tbl;
    }

    public final void collectPrimedLocs(SemanticNode pred, Context c, ObjLongTable<SemanticNode> tbl)
    {
        switch (pred.getKind()) {
        case OpApplKind: {
            OpApplNode pred1 = (OpApplNode) pred;
            this.collectPrimedLocsAppl(pred1, c, tbl);
            return;
        }
        case LetInKind: {
            LetInNode pred1 = (LetInNode) pred;
            this.collectPrimedLocs(pred1.getBody(), c, tbl);
            return;
        }
        case SubstInKind: {
            SubstInNode pred1 = (SubstInNode) pred;
            Subst[] subs = pred1.getSubsts();
            Context c1 = c;
            for (int i = 0; i < subs.length; i++)
            {
                Subst sub = subs[i];
                c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true, toolId));
            }
            this.collectPrimedLocs(pred1.getBody(), c, tbl);
            return;
        }

        // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
        case APSubstInKind: {
            APSubstInNode pred1 = (APSubstInNode) pred;
            Subst[] subs = pred1.getSubsts();
            Context c1 = c;
            for (int i = 0; i < subs.length; i++)
            {
                Subst sub = subs[i];
                c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true, toolId));
            }
            this.collectPrimedLocs(pred1.getBody(), c, tbl);
            return;
        }


            /***********************************************************************
            * LabelKind case added by LL on 13 Jun 2007.                           *
            ***********************************************************************/
        case LabelKind: {
            LabelNode pred1 = (LabelNode) pred;
            this.collectPrimedLocs(pred1.getBody(), c, tbl);
            return;
        }
        }
    }

    private final void collectPrimedLocsAppl(OpApplNode pred, Context c, ObjLongTable<SemanticNode> tbl)
    {
        ExprOrOpArgNode[] args = pred.getArgs();
        SymbolNode opNode = pred.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        switch (opcode) {
        case OPCODE_fa: // FcnApply
        {
            this.collectPrimedLocs(args[0], c, tbl);
            break;
        }
        case OPCODE_ite: // IfThenElse
        {
            this.collectPrimedLocs(args[1], c, tbl);
            this.collectPrimedLocs(args[2], c, tbl);
            break;
        }
        case OPCODE_case: // Case
        {
            for (int i = 0; i < args.length; i++)
            {
                OpApplNode pair = (OpApplNode) args[i];
                this.collectPrimedLocs(pair.getArgs()[1], c, tbl);
            }
            break;
        }
        case OPCODE_eq:   // x' = 42
        case OPCODE_in: { // x' \in S (eq case "falls through")
            SymbolNode var = this.getPrimedVar(args[0], c, false);
            if (var != null && var.getName().getVarLoc() != -1)
            {
                tbl.put(pred, 0);
            }
            break;
        }
        case OPCODE_cl: // ConjList
        case OPCODE_dl: // DisjList
        case OPCODE_be: // BoundedExists
        case OPCODE_bf: // BoundedForall
        case OPCODE_land:
        case OPCODE_lor:
        case OPCODE_implies:
        case OPCODE_nop: // This case added 13 Nov 2009 by LL to handle subexpression names.
          {
            for (int i = 0; i < args.length; i++)
            {
                this.collectPrimedLocs(args[i], c, tbl);
            }
            break;
        }
        case OPCODE_unchanged: {
            this.collectUnchangedLocs(args[0], c, tbl);
            break;
        }
        case OPCODE_aa: // AngleAct <A>_e
        {
            this.collectPrimedLocs(args[0], c, tbl);
            break;
        }
        case OPCODE_sa: // [A]_e
        {
            this.collectPrimedLocs(args[0], c, tbl);
            tbl.put(args[1], 0);
            break;
        }
        default: {
            if (opcode == 0)
            {
                Object val = this.lookup(opNode, c, false, toolId);

                if (val instanceof OpDefNode)
                {
                    OpDefNode opDef = (OpDefNode) val;
                    // Following added by LL on 10 Apr 2010 to avoid infinite 
                    // recursion for recursive operator definitions
                    if (opDef.getInRecursive()) {
                        return ;
                    }
                    Context c1 = this.getOpContext(opDef, args, c, true, toolId);
                    this.collectPrimedLocs(opDef.getBody(), c1, tbl);
                } else if (val instanceof LazyValue)
                {
                    LazyValue lv = (LazyValue) val;
                    this.collectPrimedLocs(lv.expr, lv.con, tbl);
                }
            }
        }
        }
    }

	private final void collectUnchangedLocs(final SemanticNode expr, final Context c,
			final ObjLongTable<SemanticNode> tbl) {
        if (expr instanceof OpApplNode)
        {
            OpApplNode expr1 = (OpApplNode) expr;
            SymbolNode opNode = expr1.getOperator();
            UniqueString opName = opNode.getName();
            int opcode = BuiltInOPs.getOpCode(opName);

            if (opName.getVarLoc() >= 0)
            {
                // a state variable:
                tbl.put(expr, 0);
                return;
            }

            ExprOrOpArgNode[] args = expr1.getArgs();
            if (opcode == OPCODE_tup)
            {
				// a tuple, might be:
            	// UNCHANGED <<x,y,z>>
            	// or:
            	// vars == <<x,y,z>>
            	// ...
            	// UNCHANGED vars
				// For the latter, we don't want vars == <<x,y,z>> to show up, but the vars in
				// UNCHANGED vars (see CoverageStatisticsTest).
                for (int i = 0; i < args.length; i++)
                {
               		this.collectUnchangedLocs(args[i], c, tbl);
                }
                return;
            }

            if (opcode == 0 && args.length == 0)
            {
                // a 0-arity operator:
                Object val = this.lookup(opNode, c, false, toolId);
                if (val instanceof OpDefNode)
                {
                    this.collectUnchangedLocs(((OpDefNode) val).getBody(), c, tbl);
                    return;
                }
            }
        }
        return;
    }

    public FilenameToStream getResolver()
    {
        return resolver;
    }
    
    public String getRootName() {
    	return new File(this.rootFile).getName();
    }
    
    public String getRootFile() {
    	return this.rootFile;
    }

    public String getConfigFile() {
    	return this.configFile;
    }
    
    public String getSpecDir() {
    	return this.specDir;
    }
    
    public int getId() {
    	return toolId;
    }

	public List<File> getModuleFiles(final FilenameToStream resolver) {
		final List<File> result = new ArrayList<File>();
	
		final Enumeration<ParseUnit> parseUnitContext = specProcessor.getSpecObj().parseUnitContext.elements();
		while (parseUnitContext.hasMoreElements()) {
			ParseUnit pu = (ParseUnit) parseUnitContext.nextElement();
			File resolve = resolver.resolve(pu.getFileName(), false);
			result.add(resolve);
		}
		return result;
	}
}
