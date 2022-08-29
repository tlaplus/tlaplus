// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Copyright (c) 2022, Oracle and/or its affiliates.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Thu  2 Aug 2007 at 10:25:48 PST by lamport
//      modified on Fri Jan  4 22:46:57 PST 2002 by yuanyu

package tlc2.tool.impl;

import tla2sany.modanalyzer.ParseUnit;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.*;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.tool.*;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.util.*;
import tlc2.value.*;
import tlc2.value.impl.*;
import tlc2.value.impl.Enumerable.Ordering;
import util.*;
import util.Assert.TLCRuntimeException;

import java.io.File;
import java.io.Serializable;
import java.util.*;

/**
 * This class provides useful methods for tools like model checker
 * and simulator.
 * <p>
 * It's instance serves as a spec handle
 * This is one of two places in TLC, where not all messages are retrieved from the message printer,
 * but constructed just here in the code.
 */
public abstract class Tool
        implements ValueConstants, ToolGlobals, ITool, Serializable, OpDefEvaluator, SymbolNodeValueLookupProvider {


    /* Transplated from spec */

    public static final String COLLECT_STATE_INFORMATION = "COLLECT_STATE_INFORMATION";
    public static final String PROBABLISTIC_KEY = Tool.class.getName() + ".probabilistic";
    public static final Value[] EmptyArgs = new Value[0];
    /**
     * @see tlc2.tool.coverage.CostModelCreator: See note on performance.
     */
    protected static final boolean coverage = TLCGlobals.isCoverageEnabled();
    private static final long serialVersionUID = -8485049126843307912L;
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
    private static final boolean PROBABLISTIC = Boolean.getBoolean(PROBABLISTIC_KEY);
    public final TLCState EmptyState;
    protected final int toolId;
    protected final String specDir; // The spec directory.
    protected final String rootFile; // The root file of this spec.
    protected final String configFile; // The model config file.
    protected final Set<OpDefNode> processedDefs;
    // The set of OpDefNodes on which processSpec has been called.
    // Added by LL & YY on 25 June 2014 to eliminate infinite
    // loop when a recursively defined operator is used as an
    // operator argument in its own definition.
    protected final Defns defns; // Global definitions reachable from root
    protected final Defns unprocessedDefns;
    protected final SpecObj specObj;
    protected final Action nextPred; // The next state predicate.
    protected final Action[] temporals; // Fairness specifications...
    protected final String[] temporalNames; // ... and their names
    protected final Action[] impliedTemporals; // Liveness conds to check...
    protected final String[] impliedTemporalNames; // ... and their names
    protected final Action[] invariants; // Invariants to be checked...
    protected final String[] invNames; // ... and their names
    protected final Action[] impliedInits; // Implied-inits to be checked...
    protected final String[] impliedInitNames; // ... and their names
    protected final Action[] impliedActions; // Implied-actions to be checked...
    protected final String[] impliedActNames; // ... and their names
    protected final ExprNode[] modelConstraints; // Model constraints
    protected final ExprNode[] actionConstraints; // Action constraints
    protected final ExprNode[] assumptions; // Assumpt	ions
    protected final boolean[] assumptionIsAxiom; // assumptionIsAxiom[i] is true iff assumptions[i]
    protected final SemanticNode viewSpec;
    protected final SemanticNode aliasSpec;
    protected final TLAClass tlaClass; // TLA built-in classes.
    protected final ModelConfig config; // The model configuration.
    protected final ExternalModuleTable moduleTable;
    protected final ExprNode[] processedPostConditionSpecs;
    protected final OpDefNode counterExampleDef;
    protected final Hashtable<String, ParseUnit> parseUnitContext;
    protected final Map<ModuleNode, Map<OpDefOrDeclNode, Object>> constantDefns;
    protected final Action[] actions;     // the list of TLA actions.
    protected final Mode toolMode;
    private final ArrayList<Action> initPred; // The initial state predicate.
    private final FilenameToStream resolver; // takes care of path to stream resolution
    private final OpDeclNode[] variables;
    private final tla2sany.semantic.Context sanyContext;
    private final ArrayList<Action> actionVec;
    protected ModuleNode rootModule; // The root module.
    private AbstractChecker abstractChecker;
    private Simulator simulator;

    /**
     * Creates a new tool handle
     */
    public Tool(final String specFile, final String configFile) {
        this(new File(specFile), specFile, configFile, null);
    }

    public Tool(final String specFile, final String configFile, final FilenameToStream resolver) {
        this(new File(specFile), specFile, configFile, resolver);
    }

    public Tool(final String specFile, final String configFile, final FilenameToStream resolver, final Map<String, Object> params) {
        this(new File(specFile), specFile, configFile, resolver, params);
    }

    public Tool(final String specFile, final String configFile, final FilenameToStream resolver, final Mode mode, final Map<String, Object> params) {
        this(new File(specFile), specFile, configFile, resolver, mode, params);
    }

    private Tool(final File specDir, final String specFile, final String configFile, final FilenameToStream resolver) {
        this(specDir.isAbsolute() ? specDir.getParent() : "", specFile, configFile, resolver, new HashMap<>());
    }

    private Tool(final File specDir, final String specFile, final String configFile, final FilenameToStream resolver, final Map<String, Object> params) {
        this(specDir.isAbsolute() ? specDir.getParent() : "", specFile, configFile, resolver, params);
    }

    private Tool(final File specDir, final String specFile, final String configFile, final FilenameToStream resolver, final Mode mode, final Map<String, Object> params) {
        this(specDir.isAbsolute() ? specDir.getParent() : "", specFile, configFile, resolver, mode, params);
    }

    public Tool(final String specDir, final String specFile, final String configFile, final FilenameToStream resolver, final Map<String, Object> params) {
        this(specDir, specFile, configFile, resolver, Mode.MC, params);
    }

    public Tool(final String specDir, final String specFile, final String configFile, final FilenameToStream resolver, final Mode mode, final Map<String, Object> params) {
        this.toolId = FrontEnd.getToolId();
        this.specDir = specDir;
        this.rootFile = specFile;
        this.defns = new Defns();
        this.tlaClass = new TLAClass("tlc2.module", resolver);
        this.processedDefs = new HashSet<>();
        this.resolver = resolver;

        // Reset unique string to allow this parse
        UniqueString.resetLocations();

        // SZ Mar 9, 2009: added initialization of the modelValue class
        this.configFile = configFile;
        this.config = new ModelConfig(MonolithSpecExtractor.getConfig(configFile), resolver);
        this.config.parse();
        ModelValue.setValues(); // called after seeing all model values

        // construct new specification object, if the
        // passed one was null
        final SpecObj specObj;
        if (params.isEmpty()) {
            specObj = new SpecObj(this.rootFile, resolver);
        } else {
            specObj = new ParameterizedSpecObj(this, resolver, params);
        }
        var specProcessor = new SpecProcessor(getRootName(), resolver, toolId, defns, config, this, tlaClass, mode, specObj);

        // Parse and process this spec.
        // It takes care of all overrides.
        specProcessor.processSpec(mode);
        this.variables = specProcessor.variablesNodes;

        specProcessor.snapshot();

        this.unprocessedDefns = specProcessor.getUnprocessedDefns();
        this.viewSpec = generateViewSpec(this.config, this.defns);

        if (mode == Mode.Simulation || mode == Mode.MC_DEBUG || params.containsKey(COLLECT_STATE_INFORMATION)) {
            EmptyState = TLCStateMutExt.getEmpty(this.variables, this);
        } else if (specProcessor.hasCallableValue) {
            assert mode == Mode.Executor;
            EmptyState = TLCStateMutExt.getEmpty(this.variables, this);
        } else {
            assert mode == Mode.MC;
            EmptyState = TLCStateMut.getEmpty(this.variables, this);
        }

        specProcessor.processSpec2();


        specProcessor.processConstantDefns(this);

        // Finally, process the config file.
        specProcessor.processConfig();


        this.modelConstraints = specProcessor.getModelConstraints();
        this.initPred = specProcessor.getInitPred();
        this.nextPred = specProcessor.getNextPred();
        this.actionConstraints = specProcessor.getActionConstraints();
        this.rootModule = specProcessor.getRootModule();
        this.specObj = specProcessor.getSpecObj();
        this.moduleTable = specProcessor.getModuleTbl();
        this.temporals = specProcessor.getTemporal();
        this.temporalNames = specProcessor.getImpliedTemporalNames();
        this.impliedTemporals = specProcessor.getImpliedTemporals();
        this.impliedTemporalNames = specProcessor.getImpliedTemporalNames();
        this.invariants = specProcessor.getInvariants();
        this.invNames = specProcessor.getInvariantsNames();
        this.impliedInits = specProcessor.getImpliedInits();
        this.impliedInitNames = specProcessor.getImpliedInitNames();
        this.impliedActions = specProcessor.getImpliedActions();
        this.impliedActNames = specProcessor.getImpliedActionNames();
        this.assumptions = specProcessor.getAssumptions();
        var postConditionSpecs = specProcessor.getPostConditionSpecs();
        this.parseUnitContext = specProcessor.getSpecObj().parseUnitContext;
        this.assumptionIsAxiom = specProcessor.getAssumptionIsAxiom();


        this.aliasSpec = generateAliasSpec(this.config, this.defns);
        this.processedPostConditionSpecs = generatePostConditionSpecs(this.config, this.defns, postConditionSpecs);
        this.counterExampleDef = generateCounterExampleDef(this.defns);


        this.constantDefns = specProcessor.getConstantDefns();


        this.actionVec = new ArrayList<>(10);
        this.toolMode = mode;

        final Action next = this.getNextStateSpec();
        if (next == null) {
            this.actions = new Action[0];
        } else {
            this.getActions(next);
            this.actions = new Action[this.actionVec.size()];
            this.actionVec.toArray(this.actions);
        }

        // Tag the initial predicates and next-state actions.
        final ArrayList<Action> initAndNext = new ArrayList<>(getInitStateSpec());
        initAndNext.addAll(actionVec);

        for (int i = 0; i < initAndNext.size(); i++) {
            initAndNext.get(i).setId(i);
        }

        this.sanyContext = specProcessor.sany.context;
    }

    protected Tool(final Tool other) {
        this.toolId = other.toolId;
        this.specDir = other.specDir;
        this.rootFile = other.rootFile;
        this.configFile = other.configFile;
        this.processedDefs = other.processedDefs;
        this.defns = other.defns;
        this.tlaClass = other.tlaClass;
        this.resolver = other.resolver;
        this.unprocessedDefns = other.unprocessedDefns;
        this.config = other.config;
        this.variables = other.variables;
        this.modelConstraints = other.modelConstraints;
        this.initPred = other.initPred;
        this.nextPred = other.nextPred;
        this.actionConstraints = other.actionConstraints;
        this.rootModule = other.rootModule;
        this.specObj = other.specObj;
        this.moduleTable = other.moduleTable;
        this.temporals = other.temporals;
        this.temporalNames = other.temporalNames;
        this.impliedTemporals = other.impliedTemporals;
        this.impliedTemporalNames = other.impliedTemporalNames;
        this.impliedInits = other.impliedInits;
        this.impliedInitNames = other.impliedInitNames;
        this.invariants = other.invariants;
        this.invNames = other.invNames;
        this.impliedActions = other.impliedActions;
        this.impliedActNames = other.impliedActNames;
        this.assumptions = other.assumptions;
        this.processedPostConditionSpecs = other.processedPostConditionSpecs;
        this.counterExampleDef = other.counterExampleDef;

        this.parseUnitContext = other.parseUnitContext;
        this.assumptionIsAxiom = other.assumptionIsAxiom;

        this.aliasSpec = other.aliasSpec;
        this.viewSpec = other.viewSpec;

        this.constantDefns = other.constantDefns;
        this.EmptyState = other.EmptyState;
        this.actions = other.actions;
        this.actionVec = other.actionVec;
        this.toolMode = other.toolMode;
        this.sanyContext = other.sanyContext;
    }

    private static SemanticNode generateViewSpec(ModelConfig config, Defns defns) {
        final String name = config.getView();
        if (name.length() == 0)
            return null;

        final Object view = defns.get(name);
        if (view == null) {
            Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[]{"view function", name});
        }

        if (!(view instanceof OpDefNode)) {
            Assert.fail(EC.TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT, new String[]{"view function", name});
        }
        final OpDefNode def = (OpDefNode) view;
        if (def.getArity() != 0) {
            Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[]{"view function", name});
        }
        return def.getBody();
    }

    public static SemanticNode generateAliasSpec(ModelConfig config, Defns defns) {
        final String name = config.getAlias();
        if (name.length() == 0) {
            return null;//Assert.fail(EC.TLC_CONFIG_NO_STATE_TYPE);
        }

        // A true constant-level alias such as such as [ x |-> "foo" ] will be evaluated
        // eagerly and type be an instance of RecordValue.  It would be good to return a
        // proper warning.
        final Object type = defns.get(name);
        if (type == null) {
            Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[]{"alias", name});
        }
        if (!(type instanceof OpDefNode)) {
            Assert.fail(EC.TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT, new String[]{"alias", name});
        }
        final OpDefNode def = (OpDefNode) type;
        if (def.getArity() != 0) {
            Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[]{"alias", name});
        }
        return def.getBody();
    }

    private static ExprNode[] generatePostConditionSpecs(ModelConfig config, Defns defns, List<ExprNode> res) {

        final String name = config.getPostCondition();
        if (name.length() != 0) {
            final Object type = defns.get(name);
            if (type == null) {
                Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[]{"post condition", name});
            }
            if (!(type instanceof OpDefNode)) {
                Assert.fail(EC.TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT, new String[]{"post condition", name});
            }
            final OpDefNode def = (OpDefNode) type;
            if (def.getArity() != 0) {
                Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[]{"post condition", name});

            }
            res.add(def.getBody());
        }

        return res.toArray(ExprNode[]::new);
    }

    private static OpDefNode generateCounterExampleDef(Defns defns) {
        // Defined in TLCExt.tla
        final Object type = defns.get("CounterExample");
        if (type == null) {
            // Not used anywhere in the current spec.
            return null;
        }
        if (!(type instanceof EvaluatingValue)) {
            Assert.fail(EC.GENERAL);
        }
        final OpDefNode def = ((EvaluatingValue) type).getOpDef();
        if (def.getArity() != 0) {
            Assert.fail(EC.GENERAL);
        }
        return def;
    }

    public static boolean isProbabilistic() {
        return PROBABLISTIC;
    }

    public tla2sany.semantic.Context getSANYContext() {
        return sanyContext;
    }

    public OpDeclNode[] getVariables() {
        return variables;
    }

    public TLCState getEmptyState() {
        return this.EmptyState;
    }

    public TLCState createEmptyState() {
        return this.EmptyState.createEmpty();
    }

    public ModelConfig getModelConfig() {
        return config;
    }

    /* Return the variable if expr is a primed state variable. Otherwise, null. */
    public final SymbolNode getPrimedVar(final SemanticNode expr, final Context c, final boolean cutoff) {
        if (expr instanceof final OpApplNode expr1) {
            final SymbolNode opNode = expr1.getOperator();

            if (BuiltInOPs.getOpCode(opNode.getName()) == OPCODE_prime) {
                return this.getVar(expr1.getArgs()[0], c, cutoff, toolId);
            }

            if (opNode.getArity() == 0) {
                final boolean isVarDecl = (opNode.getKind() == VariableDeclKind);
                final Object val = this.lookup(opNode, c, cutoff && isVarDecl, toolId);

                if (val instanceof final LazyValue lval) {
                    return this.getPrimedVar(lval.expr, lval.con, cutoff);
                }
                if (val instanceof OpDefNode odn) {
                    return this.getPrimedVar(odn.getBody(), c, cutoff);
                }
            }
        }
        return null;
    }

    public ModuleNode getRootModule() {
        return rootModule;
    }

    public final Map<ModuleNode, Map<OpDefOrDeclNode, Object>> getConstantDefns() {
        return constantDefns;
    }

    public Defns getDefns() {
        return defns;
    }

    public Action getNextPred() {
        return nextPred;
    }

    /**
     * Get model constraints.
     */
    public final ExprNode[] getModelConstraints() {
        return modelConstraints;
    }

    /**
     * Get action constraints.
     */
    public final ExprNode[] getActionConstraints() {
        return actionConstraints;
    }

    /* Get the initial state predicate of the specification.  */
    public final ArrayList<Action> getInitStateSpec() {
        return initPred;
    }

    /* Get the action (next state) predicate of the specification. */
    public final Action getNextStateSpec() {
        return nextPred;
    }

    /**
     * Get the view mapping for the specification.
     */
    public final SemanticNode getViewSpec() {
        return viewSpec;
    }

    /* Get the alias declaration for the state variables. */
    public final SemanticNode getAliasSpec() {
        return aliasSpec;
    }

    public final ExprNode[] getPostConditionSpecs() {
        return this.processedPostConditionSpecs;
    }

    public final OpDefNode getCounterExampleDef() {
        return this.counterExampleDef;
    }

    public ExternalModuleTable getModuleTbl() {
        return moduleTable;
    }

    public final boolean livenessIsTrue() {
        return getImpliedTemporals().length == 0;
    }

    /* Get the fairness condition of the specification.  */
    public final Action[] getTemporals() {
        return temporals;
    }

    public ArrayList<Action> getInitPred() {
        return initPred;
    }

    public final String[] getTemporalNames() {
        return temporalNames;
    }

    /* Get the liveness checks of the specification.  */
    public final Action[] getImpliedTemporals() {
        return impliedTemporals;
    }

    public final String[] getImpliedTemporalNames() {
        return impliedTemporalNames;
    }

    /* Get the invariants of the specification. */
    public final Action[] getInvariants() {
        return invariants;
    }

    public final String[] getInvNames() {
        return invNames;
    }

    /* Get the implied-inits of the specification. */
    public final Action[] getImpliedInits() {
        return impliedInits;
    }

    public final String[] getImpliedInitNames() {
        return impliedInitNames;
    }

    /* Get the implied-actions of the specification. */
    public final Action[] getImpliedActions() {
        return impliedActions;
    }

    public final String[] getImpliedActNames() {
        return impliedActNames;
    }

    /* Get the assumptions of the specification. */
    public final ExprNode[] getAssumptions() {
        return assumptions;
    }

    /* Get the assumptionIsAxiom field */
    public final boolean[] getAssumptionIsAxiom() {
        return assumptionIsAxiom;
    }

    /**
     * This method gets the value of a symbol from the environment. We
     * look up in the context c, its tool object, and the state s.
     * <p>
     * It and the lookup method that follows it were modified by LL
     * on 10 April 2011 to fix the following bug.  When a constant definition
     * Foo == ...
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
     */
    public final Object lookup(final SymbolNode opNode, final Context c, final TLCState s, final boolean cutoff) {
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

    public final Object lookup(final SymbolNode opNode) {
        return lookup(opNode, Context.Empty, false, toolId);
    }

    /**
     * The following added by LL on 23 October 2012 to fix bug in evaluation of names of theorems and
     * assumptions imported by parameterized instantiation.
     */
    public final Context getOpContext(final ThmOrAssumpDefNode opDef, final ExprOrOpArgNode[] args, final Context c, final boolean cachable) {
        final FormalParamNode[] formals = opDef.getParams();
        final int alen = args.length;
        Context c1 = c;
        for (int i = 0; i < alen; i++) {
            final Object aval = this.getVal(args[i], c, cachable, toolId);
            c1 = c1.cons(formals[i], aval);
        }
        return c1;
    }

    /**
     * Return a table containing the locations of subexpression in the
     * spec of forms x' = e and x' \in e. Warning: Current implementation
     * may not be able to find all such locations.
     */
    public final ObjLongTable<SemanticNode> getPrimedLocs() {
        final ObjLongTable<SemanticNode> tbl = new ObjLongTable<>(10);
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

    public final void collectPrimedLocs(final SemanticNode pred, final Context c, final ObjLongTable<SemanticNode> tbl) {
        switch (pred.getKind()) {
            case OpApplKind -> {
                final OpApplNode pred1 = (OpApplNode) pred;
                this.collectPrimedLocsAppl(pred1, c, tbl);
            }
            case LetInKind -> {
                final LetInNode pred1 = (LetInNode) pred;
                this.collectPrimedLocs(pred1.getBody(), c, tbl);
            }
            case SubstInKind -> {
                final SubstInNode pred1 = (SubstInNode) pred;
                final Subst[] subs = pred1.getSubsts();
                Context c1 = c;
                for (final Subst sub : subs) {
                    c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true, toolId));
                }
                this.collectPrimedLocs(pred1.getBody(), c, tbl);
            }


            // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
            case APSubstInKind -> {
                final APSubstInNode pred1 = (APSubstInNode) pred;
                final Subst[] subs = pred1.getSubsts();
                Context c1 = c;
                for (final Subst sub : subs) {
                    c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true, toolId));
                }
                this.collectPrimedLocs(pred1.getBody(), c, tbl);
            }


            /***********************************************************************
             * LabelKind case added by LL on 13 Jun 2007.                           *
             ***********************************************************************/
            case LabelKind -> {
                final LabelNode pred1 = (LabelNode) pred;
                this.collectPrimedLocs(pred1.getBody(), c, tbl);
            }
        }
    }

    private void collectPrimedLocsAppl(final OpApplNode pred, final Context c, final ObjLongTable<SemanticNode> tbl) {
        final ExprOrOpArgNode[] args = pred.getArgs();
        final SymbolNode opNode = pred.getOperator();
        final int opcode = BuiltInOPs.getOpCode(opNode.getName());

        switch (opcode) { // FcnApply
            case OPCODE_fa, OPCODE_aa -> // AngleAct <A>_e
                    this.collectPrimedLocs(args[0], c, tbl);
            case OPCODE_ite -> // IfThenElse
            {
                this.collectPrimedLocs(args[1], c, tbl);
                this.collectPrimedLocs(args[2], c, tbl);
            }
            case OPCODE_case -> // Case
            {
                for (final ExprOrOpArgNode arg : args) {
                    final OpApplNode pair = (OpApplNode) arg;
                    this.collectPrimedLocs(pair.getArgs()[1], c, tbl);
                }
            }
            // x' = 42
            case OPCODE_eq, OPCODE_in -> { // x' \in S (eq case "falls through")
                final SymbolNode var = this.getPrimedVar(args[0], c, false);
                if (var != null && var.getName().getVarLoc(variables.length) != -1) {
                    tbl.put(pred, 0);
                }
            }
            // ConjList
            // DisjList
            // BoundedExists
            // BoundedForall
            case OPCODE_cl, OPCODE_dl, OPCODE_be, OPCODE_bf, OPCODE_land, OPCODE_lor, OPCODE_implies, OPCODE_nop -> // This case added 13 Nov 2009 by LL to handle subexpression names.
            {
                for (final ExprOrOpArgNode arg : args) {
                    this.collectPrimedLocs(arg, c, tbl);
                }
            }
            case OPCODE_unchanged -> this.collectUnchangedLocs(args[0], c, tbl);
            case OPCODE_sa -> // [A]_e
            {
                this.collectPrimedLocs(args[0], c, tbl);
                tbl.put(args[1], 0);
            }
            default -> {
                if (opcode == 0) {
                    final Object val = this.lookup(opNode, c, false, toolId);

                    if (val instanceof final OpDefNode opDef) {
                        // Following added by LL on 10 Apr 2010 to avoid infinite
                        // recursion for recursive operator definitions
                        if (opDef.getInRecursive()) {
                            return;
                        }
                        final Context c1 = this.getOpContext(opDef, args, c, true, toolId);
                        this.collectPrimedLocs(opDef.getBody(), c1, tbl);
                    } else if (val instanceof final LazyValue lv) {
                        this.collectPrimedLocs(lv.expr, lv.con, tbl);
                    }
                }
            }
        }
    }

    private void collectUnchangedLocs(final SemanticNode expr, final Context c,
                                      final ObjLongTable<SemanticNode> tbl) {
        if (expr instanceof final OpApplNode expr1) {
            final SymbolNode opNode = expr1.getOperator();
            final UniqueString opName = opNode.getName();
            final int opcode = BuiltInOPs.getOpCode(opName);

            if (opName.getVarLoc(variables.length) >= 0) {
// a state variable:
                tbl.put(expr, 0);
                return;
            }

            final ExprOrOpArgNode[] args = expr1.getArgs();
            if (opcode == OPCODE_tup) {
                // a tuple, might be:
                // UNCHANGED <<x,y,z>>
                // or:
                // vars == <<x,y,z>>
                // ...
                // UNCHANGED vars
                // For the latter, we don't want vars == <<x,y,z>> to show up, but the vars in
                // UNCHANGED vars (see CoverageStatisticsTest).
                for (final ExprOrOpArgNode arg : args) {
                    this.collectUnchangedLocs(arg, c, tbl);
                }
                return;
            }

            if (opcode == 0 && args.length == 0) {
// a 0-arity operator:
                final Object val = this.lookup(opNode, c, false, toolId);
                if (val instanceof OpDefNode odn) {
                    this.collectUnchangedLocs(odn.getBody(), c, tbl);
                }
            }
        }
    }

    public FilenameToStream getResolver() {
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

    public ModuleNode getModule(final String moduleName) {
        return moduleTable.getModuleNode(moduleName);
    }

    public List<File> getModuleFiles(final FilenameToStream resolver) {
        final List<File> result = new ArrayList<>();

        final Enumeration<ParseUnit> parseUnitContextElements = parseUnitContext.elements();
        while (parseUnitContextElements.hasMoreElements()) {
            final ParseUnit pu = parseUnitContextElements.nextElement();
            final File resolve = resolver.resolve(pu.getFileName(), false);
            result.add(resolve);
        }
        return result;
    }

    @Override
    public ITool getFingerprintingTool() {
        return this;
    }

    @Override
    public AbstractChecker getMainChecker() {
        return abstractChecker;
    }

    @Override
    public void setMainChecker(AbstractChecker abstractChecker) {
        this.abstractChecker = abstractChecker;
    }

    @Override
    public Simulator getSimulator() {
        return simulator;
    }

    @Override
    public void setSimulator(Simulator simulator) {
        this.simulator = simulator;
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

    private void getActions(final Action next) {
        this.getActions(next.pred, next.con, next.getOpDef(), next.cm);
    }

    private void getActions(final SemanticNode next, final Context con, final OpDefNode opDefNode, final CostModel cm) {
        switch (next.getKind()) {
            case OpApplKind -> {
                final OpApplNode next1 = (OpApplNode) next;
                this.getActionsAppl(next1, con, opDefNode, cm);
            }
            case LetInKind -> {
                final LetInNode next1 = (LetInNode) next;
                this.getActions(next1.getBody(), con, opDefNode, cm);
            }
            case SubstInKind -> {
                final SubstInNode next1 = (SubstInNode) next;
                final Subst[] substs = next1.getSubsts();
                if (substs.length == 0) {
                    this.getActions(next1.getBody(), con, opDefNode, cm);
                } else {
                    final Action action = new Action(next1, con, opDefNode);
                    this.actionVec.add(action);
                }
            }


            // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
            case APSubstInKind -> {
                final APSubstInNode next1 = (APSubstInNode) next;
                final Subst[] substs = next1.getSubsts();
                if (substs.length == 0) {
                    this.getActions(next1.getBody(), con, opDefNode, cm);
                } else {
                    final Action action = new Action(next1, con, opDefNode);
                    this.actionVec.add(action);
                }
            }


            /***********************************************************************
             * LabelKind class added by LL on 13 Jun 2007.                          *
             ***********************************************************************/
            case LabelKind -> {
                final LabelNode next1 = (LabelNode) next;
                this.getActions(next1.getBody(), con, opDefNode, cm);
            }
            default -> Assert.fail("The next state relation is not a boolean expression.\n" + next, next, con);
        }
    }

    private void getActionsAppl(final OpApplNode next, final Context con, final OpDefNode actionName, final CostModel cm) {
        final ExprOrOpArgNode[] args = next.getArgs();
        final SymbolNode opNode = next.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        if (opcode == 0) {
            final Object val = this.lookup(opNode, con, false);

            if (val instanceof final OpDefNode opDef) {
                opcode = BuiltInOPs.getOpCode(opDef.getName());
                if (opcode == 0) {
                    try {
                        final FormalParamNode[] formals = opDef.getParams();
                        final int alen = args.length;
                        int argLevel = 0;
                        for (final ExprOrOpArgNode arg : args) {
                            argLevel = arg.getLevel();
                            if (argLevel != 0) break;
                        }
                        if (argLevel == 0) {
                            Context con1 = con;
                            for (int i = 0; i < alen; i++) {
                                final IValue aval = this.eval(args[i], con, EmptyState, cm);
                                con1 = con1.cons(formals[i], aval);
                            }
                            this.getActions(opDef.getBody(), con1, opDef, cm);
                            return;
                        }
                    } catch (final Throwable e) { /*SKIP*/ }
                }
            }
            if (opcode == 0) {
                final Action action = new Action(next, con, (OpDefNode) opNode);
                this.actionVec.add(action);
                return;
            }
        }

        switch (opcode) {
            case OPCODE_be ->     // BoundedExists
            {
                final int cnt = this.actionVec.size();
                try {
                    final IContextEnumerator contextEnumerator =
                            this.contexts(next, con, EmptyState, EmptyState, EvalControl.Clear, cm);

                    if (!contextEnumerator.hasNext()) {
                        // No exception and no actions created implies contextEnumerator was empty:
                        // \E i \in {} : ...
                        // \E i \in Nat: FALSE
                        // ...
                        this.actionVec.add(new Action(next, con, actionName));
                        return;
                    }

                    while (contextEnumerator.hasNext()) {
                        Context econ = contextEnumerator.next();
                        this.getActions(args[0], econ, actionName, cm);
                    }
                    assert (cnt < this.actionVec.size())
                            : "AssertionError when creating Actions. This case should have been handled by contextEnumerator.isDone conditional above!";
                } catch (final Throwable e) {
                    final Action action = new Action(next, con, actionName);

                    // Remove all elements except the first count
                    if (this.actionVec.size() > cnt) {
                        this.actionVec.subList(cnt, this.actionVec.size()).clear();
                    }

                    this.actionVec.add(action);
                }
            }
            // DisjList
            case OPCODE_dl, OPCODE_lor -> {
                for (final ExprOrOpArgNode arg : args) {
                    this.getActions(arg, con, actionName, cm);
                }
            }
            default -> {
                // We handle all the other builtin operators here.
                final Action action = new Action(next, con, actionName);
                this.actionVec.add(action);
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
    public final void getInitStates(final IStateFunctor functor) {
        final ArrayList<Action> init = this.getInitStateSpec();
        ActionItemList acts = ActionItemListExt.Empty.getEmpty();
        // MAK 09/11/2018: Tail to head iteration order cause the first elem added with
        // acts.cons to be acts tail. This fixes the bug/funny behavior that the init
        // predicate Init == A /\ B /\ C /\ D was evaluated in the order A, D, C, B (A
        // doesn't get added to acts at all).
        for (int i = (init.size() - 1); i > 0; i--) {
            final Action elem = init.get(i);
            acts = acts.cons(elem, IActionItemList.PRED);
        }
        if (!init.isEmpty()) {
            final Action elem = init.get(0);
            final TLCState ps = this.createEmptyState();
            if (acts.isEmpty()) {
                acts.setAction(elem);
            }
            this.getInitStates(elem.pred, acts, elem.con, ps, functor, elem.cm);
        }
    }

    /* Create the state specified by pred.  */
    @Override
    public final TLCState makeState(final SemanticNode pred) {
        final ActionItemList acts = ActionItemList.Empty.getEmpty();
        final TLCState ps = this.createEmptyState();
        final StateVec states = new StateVec(0);
        this.getInitStates(pred, acts, Context.Empty, ps, states, acts.cm);
        if (states.size() != 1) {
            Assert.fail("The predicate does not specify a unique state." + pred, pred);
        }
        final TLCState state = states.get(0);
        if (!this.isGoodState(state)) {
            Assert.fail("The state specified by the predicate is not complete." + pred, pred);
        }
        return state;
    }

    protected void getInitStates(final SemanticNode init, final ActionItemList acts,
                                 final Context c, final TLCState ps, final IStateFunctor states, final CostModel cm) {
        switch (init.getKind()) {
            case OpApplKind -> {
                final OpApplNode init1 = (OpApplNode) init;
                this.getInitStatesAppl(init1, acts, c, ps, states, cm);
            }
            case LetInKind -> {
                final LetInNode init1 = (LetInNode) init;
                this.getInitStates(init1.getBody(), acts, c, ps, states, cm);
            }
            case SubstInKind -> {
                final SubstInNode init1 = (SubstInNode) init;
                final Subst[] subs = init1.getSubsts();
                Context c1 = c;
                for (final Subst sub : subs) {
                    c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, coverage ? sub.getCM() : cm, toolId));
                }
                this.getInitStates(init1.getBody(), acts, c1, ps, states, cm);
            }

            // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
            case APSubstInKind -> {
                final APSubstInNode init1 = (APSubstInNode) init;
                final Subst[] subs = init1.getSubsts();
                Context c1 = c;
                for (final Subst sub : subs) {
                    c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, cm, toolId));
                }
                this.getInitStates(init1.getBody(), acts, c1, ps, states, cm);
            }

            // LabelKind class added by LL on 13 Jun 2007
            case LabelKind -> {
                final LabelNode init1 = (LabelNode) init;
                this.getInitStates(init1.getBody(), acts, c, ps, states, cm);
            }
            default -> Assert.fail("The init state relation is not a boolean expression.\n" + init, init, c);
        }
    }

    protected void getInitStates(ActionItemList acts, final TLCState ps, final IStateFunctor states, final CostModel cm) {
        if (acts.isEmpty()) {
            if (coverage) {
                cm.incInvocations();
                cm.getRoot().incInvocations();
            }
            states.addState(ps.copy().setAction(acts.getAction()));
            return;
        } else if (ps.allAssigned()) {
            // MAK 05/25/2018: If all values of the initial state have already been
            // assigned, there is no point in further trying to assign values. Instead, all
            // remaining statements (ActionItemList) can just be evaluated for their boolean
            // value.
            // This optimization is especially useful to check inductive invariants which
            // require TLC to generate a very large set of initial states.
            while (!acts.isEmpty()) {
                final Value bval = this.eval(acts.carPred(), acts.carContext(), ps, EmptyState, EvalControl.Init, acts.cm);
                if (!(bval instanceof BoolValue)) {
                    //TODO Choose more fitting error message.
                    Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING,
                            new String[]{"initial states", "boolean", bval.toString(), acts.pred.toString()}, acts.carPred(), acts.carContext());
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
            states.addState(ps.copy().setAction(acts.getAction()));
            return;
        }
        // Assert.check(act.kind > 0 || act.kind == -1);
        final ActionItemList acts1 = acts.cdr();
        this.getInitStates(acts.carPred(), acts1, acts.carContext(), ps, states, acts.cm);
    }

    protected void getInitStatesAppl(final OpApplNode init, ActionItemList acts,
                                     final Context c, TLCState ps, final IStateFunctor states, CostModel cm) {
        if (coverage) {
            cm = cm.get(init);
        }
        final ExprOrOpArgNode[] args = init.getArgs();
        final int alen = args.length;
        final SymbolNode opNode = init.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        if (opcode == 0) {
            // This is a user-defined operator with one exception: it may
            // be substed by a builtin operator. This special case occurs
            // when the lookup returns an OpDef with opcode # 0.
            Object val = this.lookup(opNode, c, ps, false);

            if (val instanceof final OpDefNode opDef) {
                opcode = BuiltInOPs.getOpCode(opDef.getName());
                if (opcode == 0) {
                    // Context c1 = this.getOpContext(opDef, args, c, false);
                    final Context c1 = this.getOpContext(opDef, args, c, true, cm, toolId);
                    this.getInitStates(opDef.getBody(), acts, c1, ps, states, cm);
                    return;
                }
            }
            // Added 13 Nov 2009 by LL to fix Yuan's fix.
            /*********************************************************************
             * Modified on 23 October 2012 by LL to work if ThmOrAssumpDefNode    *
             * imported with parameterized instantiation.                         *
             *********************************************************************/
            if (val instanceof final ThmOrAssumpDefNode opDef) {
                final Context c1 = this.getOpContext(opDef, args, c, true);
                this.getInitStates(opDef.getBody(), acts, c1, ps, states, cm);
                return;
            }

            if (val instanceof final LazyValue lv) {
                if (lv.getValue() == null || lv.isUncachable()) {
                    this.getInitStates(lv.expr, acts, lv.con, ps, states, cm);
                    return;
                }
                val = lv.getValue();
            }

            Object bval = val;
            if (alen == 0) {
                if (val instanceof MethodValue mv) {
                    bval = mv.apply(EmptyArgs, EvalControl.Init);
                } else if (val instanceof EvaluatingValue ev) {
                    // Allow EvaluatingValue overwrites to have zero arity.
                    bval = ev.eval(this, args, c, ps, EmptyState, EvalControl.Init, cm);
                }
            } else {
                if (val instanceof OpValue ov) {
                    bval = ov.eval(this, args, c, ps, EmptyState, EvalControl.Init, cm);
                }
            }

            if (opcode == 0) {
                if (!(bval instanceof BoolValue)) {
                    Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[]{"initial states", "boolean",
                            bval.toString(), init.toString()}, init, c);
                }
                if (((BoolValue) bval).val) {
                    this.getInitStates(acts, ps, states, cm);
                }
                return;
            }
        }

        switch (opcode) {     // DisjList
            case OPCODE_dl, OPCODE_lor -> {
                for (final ExprOrOpArgNode arg : args) {
                    this.getInitStates(arg, acts, c, ps, states, cm);
                }
            }
            // ConjList
            case OPCODE_cl, OPCODE_land -> {
                for (int i = alen - 1; i > 0; i--) {
                    acts = (ActionItemList) acts.cons(args[i], c, cm, i);
                }
                this.getInitStates(args[0], acts, c, ps, states, cm);
            }
            case OPCODE_be ->     // BoundedExists
            {
                final SemanticNode body = args[0];
                final IContextEnumerator contextEnumerator = this.contexts(init, c, ps, EmptyState, EvalControl.Init, cm);

                while (contextEnumerator.hasNext()) {
                    Context c1 = contextEnumerator.next();
                    this.getInitStates(body, acts, c1, ps, states, cm);
                }
            }
            case OPCODE_bf ->     // BoundedForall
            {
                final SemanticNode body = args[0];
                final IContextEnumerator contextEnumerator = this.contexts(init, c, ps, EmptyState, EvalControl.Init, cm);

                if (!contextEnumerator.hasNext()) {
                    this.getInitStates(acts, ps, states, cm);
                } else {
                    final Context c1 = contextEnumerator.next();

                    ActionItemList acts1 = acts;
                    while (contextEnumerator.hasNext()) {
                        Context c2 = contextEnumerator.next();
                        acts1 = (ActionItemList) acts1.cons(body, c2, cm, IActionItemList.PRED);
                    }
                    this.getInitStates(body, acts1, c1, ps, states, cm);
                }
            }
            case OPCODE_ite ->    // IfThenElse
            {
                final Value guard = this.eval(args[0], c, ps, EmptyState, EvalControl.Init, cm);
                if (!(guard instanceof BoolValue)) {
                    Assert.fail("In computing initial states, a non-boolean expression (" +
                            guard.getKindString() + ") was used as the condition " +
                            "of an IF.\n" + init, init, c);
                }
                final int idx = (((BoolValue) guard).val) ? 1 : 2;
                this.getInitStates(args[idx], acts, c, ps, states, cm);
            }
            case OPCODE_case ->   // Case
            {
                SemanticNode other = null;
                for (final ExprOrOpArgNode arg : args) {
                    final OpApplNode pair = (OpApplNode) arg;
                    final ExprOrOpArgNode[] pairArgs = pair.getArgs();
                    if (pairArgs[0] == null) {
                        other = pairArgs[1];
                    } else {
                        final Value bval = this.eval(pairArgs[0], c, ps, EmptyState, EvalControl.Init, cm);
                        if (!(bval instanceof BoolValue)) {
                            Assert.fail("In computing initial states, a non-boolean expression (" +
                                    bval.getKindString() + ") was used as a guard condition" +
                                    " of a CASE.\n" + pairArgs[1], pairArgs[1], c);
                        }
                        if (((BoolValue) bval).val) {
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
            }
            case OPCODE_fa ->     // FcnApply
            {
                Value fval = this.eval(args[0], c, ps, EmptyState, EvalControl.Init, cm);
                if (fval instanceof final FcnLambdaValue fcn) {
                    if (fcn.fcnRcd == null) {
                        final Context c1 = this.getFcnContext(fcn, args, c, ps, EmptyState, EvalControl.Init, cm);
                        this.getInitStates(fcn.body, acts, c1, ps, states, cm);
                        return;
                    }
                    fval = fcn.fcnRcd;
                } else if (!(fval instanceof Applicable)) {
                    Assert.fail("In computing initial states, a non-function (" +
                            fval.getKindString() + ") was applied as a function.\n" + init, init, c);
                }
                final Applicable fcn = (Applicable) fval;
                final Value argVal = this.eval(args[1], c, ps, EmptyState, EvalControl.Init, cm);
                final Value bval = fcn.apply(argVal, EvalControl.Init);
                if (!(bval instanceof BoolValue)) {
                    Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING2, new String[]{"initial states", "boolean",
                            init.toString()}, args[1], c);
                }
                if (((BoolValue) bval).val) {
                    this.getInitStates(acts, ps, states, cm);
                }
            }
            case OPCODE_eq -> {
                final SymbolNode var = this.getVar(args[0], c, false, toolId);
                if (var == null || var.getName().getVarLoc(variables.length) < 0) {
                    final Value bval = this.eval(init, c, ps, EmptyState, EvalControl.Init, cm);
                    if (!((BoolValue) bval).val) {
                        return;
                    }
                } else {
                    final UniqueString varName = var.getName();
                    final IValue lval = ps.lookup(varName);
                    final Value rval = this.eval(args[1], c, ps, EmptyState, EvalControl.Init, cm);
                    if (lval == null) {
                        ps = ps.bind(varName, rval);
                        this.getInitStates(acts, ps, states, cm);
                        ps.unbind(varName);
                        return;
                    } else {
                        if (!lval.equals(rval)) {
                            return;
                        }
                    }
                }
                this.getInitStates(acts, ps, states, cm);
            }
            case OPCODE_in -> {
                final SymbolNode var = this.getVar(args[0], c, false, toolId);
                if (var == null || var.getName().getVarLoc(variables.length) < 0) {
                    final Value bval = this.eval(init, c, ps, EmptyState, EvalControl.Init, cm);
                    if (!((BoolValue) bval).val) {
                        return;
                    }
                } else {
                    final UniqueString varName = var.getName();
                    final Value lval = (Value) ps.lookup(varName);
                    final Value rval = this.eval(args[1], c, ps, EmptyState, EvalControl.Init, cm);
                    if (lval == null) {
                        if (!(rval instanceof Enumerable)) {
                            Assert.fail("In computing initial states, the right side of \\IN" +
                                    " is not enumerable.\n" + init, init, c);
                        }
                        final ValueEnumeration Enum = ((Enumerable) rval).elements();
                        Value elem;
                        while ((elem = Enum.nextElement()) != null) {
                            ps.bind(varName, elem);
                            this.getInitStates(acts, ps, states, cm);
                            ps.unbind(varName);
                        }
                        return;
                    } else {
                        if (!rval.member(lval)) {
                            return;
                        }
                    }
                }
                this.getInitStates(acts, ps, states, cm);
            }
            case OPCODE_implies -> {
                final Value lval = this.eval(args[0], c, ps, EmptyState, EvalControl.Init, cm);
                if (!(lval instanceof BoolValue)) {
                    Assert.fail("In computing initial states of a predicate of form" +
                            " P => Q, P was " + lval.getKindString() + "\n." + init, init, c);
                }
                if (((BoolValue) lval).val) {
                    this.getInitStates(args[1], acts, c, ps, states, cm);
                } else {
                    this.getInitStates(acts, ps, states, cm);
                }
            }

            // The following case added by LL on 13 Nov 2009 to handle subexpression names.
            case OPCODE_nop -> this.getInitStates(args[0], acts, c, ps, states, cm);
            default -> {
                // For all the other builtin operators, simply evaluate:
                final Value bval = this.eval(init, c, ps, EmptyState, EvalControl.Init, cm);
                if (!(bval instanceof BoolValue)) {

                    Assert.fail("In computing initial states, TLC expected a boolean expression," +
                            "\nbut instead found " + bval + ".\n" + init, init, c);
                }
                if (((BoolValue) bval).val) {
                    this.getInitStates(acts, ps, states, cm);
                }
            }
        }
    }

    /**
     * This method returns the set of next states when taking the action
     * in the given state.
     */
    @Override
    public final StateVec getNextStates(final Action action, final TLCState state) {
        return getNextStates(action, action.con, state);
    }

    public final StateVec getNextStates(final Action action, final Context ctx, final TLCState state) {
        final ActionItemList acts = ActionItemList.Empty.getEmpty();
        final TLCState s1 = this.createEmptyState();
        final StateVec nss = new StateVec(0);
        this.getNextStates(action, action.pred, acts, ctx, state, s1.setPredecessor(state).setAction(action), nss, action.cm);
        if (coverage) {
            action.cm.incInvocations(nss.size());
        }
        if (PROBABLISTIC && nss.size() > 1) {
            System.err.println("Simulator generated more than one next state");
        }
        return nss;
    }

    @Override
    public boolean getNextStates(final INextStateFunctor functor, final TLCState state) {
        for (final Action action : actions) {
            this.getNextStates(functor, state, action);
        }
        return false;
    }

    @Override
    public boolean getNextStates(final INextStateFunctor functor, final TLCState state, final Action action) {
        this.getNextStates(action, action.pred, ActionItemList.Empty.getEmpty(), action.con, state,
                this.createEmptyState().setPredecessor(state).setAction(action), functor, action.cm);
        return false;
    }

    protected abstract TLCState getNextStates(final Action action, SemanticNode pred, ActionItemList acts, Context c,
                                              TLCState s0, TLCState s1, INextStateFunctor nss, CostModel cm);

    protected final TLCState getNextStatesImpl(final Action action, final SemanticNode pred, final ActionItemList acts, final Context c,
                                               final TLCState s0, final TLCState s1, final INextStateFunctor nss, CostModel cm) {
        switch (pred.getKind()) {
            case OpApplKind -> {
                final OpApplNode pred1 = (OpApplNode) pred;
                if (coverage) {
                    cm = cm.get(pred);
                }
                return this.getNextStatesAppl(action, pred1, acts, c, s0, s1, nss, cm);
            }
            case LetInKind -> {
                final LetInNode pred1 = (LetInNode) pred;
                return this.getNextStates(action, pred1.getBody(), acts, c, s0, s1, nss, cm);
            }
            case SubstInKind -> {
                return getNextStatesImplSubstInKind(action, (SubstInNode) pred, acts, c, s0, s1, nss, cm);
            }

            // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
            case APSubstInKind -> {
                return getNextStatesImplApSubstInKind(action, (APSubstInNode) pred, acts, c, s0, s1, nss, cm);
            }

            // LabelKind class added by LL on 13 Jun 2007
            case LabelKind -> {
                final LabelNode pred1 = (LabelNode) pred;
                return this.getNextStates(action, pred1.getBody(), acts, c, s0, s1, nss, cm);
            }
            default -> Assert.fail("The next state relation is not a boolean expression.\n" + pred, pred, c);
        }
        return s1;
    }

    @ExpectInlined
    private TLCState getNextStatesImplSubstInKind(final Action action, final SubstInNode pred1, final ActionItemList acts, final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
        final Subst[] subs = pred1.getSubsts();

        Context c1 = c;
        for (final Subst sub : subs) {
            c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, coverage ? sub.getCM() : cm, toolId));
        }
        return this.getNextStates(action, pred1.getBody(), acts, c1, s0, s1, nss, cm);
    }

    @ExpectInlined
    private TLCState getNextStatesImplApSubstInKind(final Action action, final APSubstInNode pred1, final ActionItemList acts, final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm) {
        final Subst[] subs = pred1.getSubsts();

        Context c1 = c;
        for (final Subst sub : subs) {
            c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, cm, toolId));
        }
        return this.getNextStates(action, pred1.getBody(), acts, c1, s0, s1, nss, cm);
    }

    @ExpectInlined
    private TLCState getNextStates(final Action action, final ActionItemList acts, final TLCState s0, final TLCState s1,
                                   final INextStateFunctor nss, final CostModel cm) {
        final TLCState copy = getNextStates0(action, acts, s0, s1, nss, cm);
        if (coverage && copy != s1) {
            cm.incInvocations();
        }
        return copy;
    }


    @ExpectInlined
    private TLCState getNextStates0(final Action action, final ActionItemList acts, final TLCState s0, final TLCState s1,
                                    final INextStateFunctor nss, CostModel cm) {
        if (acts.isEmpty()) {
            nss.addState(s0, action, s1);
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
        final SemanticNode pred = acts.carPred();
        final Context c = acts.carContext();
        final ActionItemList acts1 = acts.cdr();
        cm = acts.cm;
        if (kind > 0) {
            return this.getNextStates(action, pred, acts1, c, s0, s1, nss, cm);
        } else if (kind == -1) {
            return this.getNextStates(action, pred, acts1, c, s0, s1, nss, cm);
        } else if (kind == -2) {
            return this.processUnchanged(action, pred, acts1, c, s0, s1, nss, cm);
        } else {
            final IValue v1 = this.eval(pred, c, s0, cm);
            final IValue v2 = this.eval(pred, c, s1, cm);
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

    private TLCState getNextStatesAllAssigned(final Action action, ActionItemList acts, final TLCState s0, final TLCState s1,
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
                            new String[]{"next states", "boolean", bval.toString(), acts.pred.toString()}, pred, c);
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
        nss.addState(s0, action, s1);
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

            if (val instanceof final OpDefNode opDef) {
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
            if (val instanceof final ThmOrAssumpDefNode opDef) {
                return this.getNextStates(action, opDef.getBody(), acts, this.getOpContext(opDef, args, c, true), s0, s1, nss, cm);
            }

            if (val instanceof final LazyValue lv) {
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
            if (opcode == 0) {
                return getNextStatesApplUsrDefOp(action, pred, acts, s0, s1, nss, cm, bval);
            }
        }

        return getNextStatesApplSwitch(action, pred, acts, c, s0, s1, nss, cm, args, alen, opcode);
    }

    private Object getNextStatesApplEvalAppl(final int alen, final ExprOrOpArgNode[] args, final Context c,
                                             final TLCState s0, final TLCState s1, final CostModel cm, final Object val) {
        if (alen == 0) {
            if (val instanceof MethodValue mv) {
                return mv.apply(EmptyArgs, EvalControl.Clear);
            } else if (val instanceof EvaluatingValue ev) {
                return ev.eval(this, args, c, s0, s1, EvalControl.Clear, cm);
            }
        } else {
            if (val instanceof OpValue ov) { // EvaluatingValue sub-class of OpValue!
                return ov.eval(this, args, c, s0, s1, EvalControl.Clear, cm);
            }
        }
        return val;
    }

    private TLCState getNextStatesApplUsrDefOp(final Action action, final OpApplNode pred, final ActionItemList acts, final TLCState s0,
                                               final TLCState s1, final INextStateFunctor nss, final CostModel cm, final Object bval) {
        if (!(bval instanceof BoolValue)) {
            Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[]{"next states", "boolean",
                    bval.toString(), pred.toString()}, pred);
        }
        if (((BoolValue) bval).val) {
            if (coverage) {
                return this.getNextStates(action, acts, s0, s1, nss, cm);
            } else {
                return this.getNextStates0(action, acts, s0, s1, nss, cm);
            }
        }
        return s1;
    }

    private TLCState getNextStatesApplSwitch(final Action action, final OpApplNode pred, final ActionItemList acts, final Context c, final TLCState s0,
                                             final TLCState s1, final INextStateFunctor nss, final CostModel cm, final ExprOrOpArgNode[] args, final int alen, final int opcode) {
        TLCState resState = s1;
        switch (opcode) {     // ConjList
            case OPCODE_cl, OPCODE_land -> {
                ActionItemList acts1 = acts;
                for (int i = alen - 1; i > 0; i--) {
                    acts1 = (ActionItemList) acts1.cons(args[i], c, cm, i);
                }
                return this.getNextStates(action, args[0], acts1, c, s0, s1, nss, cm);
            }
            // DisjList
            case OPCODE_dl, OPCODE_lor -> {
                if (PROBABLISTIC) {
                    // probabilistic (return after a state has been generated, ordered is randomized)
                    final RandomGenerator rng = getSimulator().getRNG();
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
            case OPCODE_be ->     // BoundedExists
            {
                final SemanticNode body = args[0];

                if (PROBABLISTIC) {
                    // probabilistic (return after a state has been generated, ordered is randomized)
                    final IContextEnumerator contextEnumerator = this.contexts(Ordering.RANDOMIZED, pred, c, s0, s1, EvalControl.Clear, cm);
                    while (contextEnumerator.hasNext()) {
                        Context c1 = contextEnumerator.next();
                        resState = this.getNextStates(action, body, acts, c1, s0, resState, nss, cm);
                        if (nss.hasStates()) {
                            return resState;
                        }
                    }
                } else {
                    // non-deterministically generate successor states (potentially many)
                    final IContextEnumerator contextEnumerator = this.contexts(pred, c, s0, s1, EvalControl.Clear, cm);
                    while (contextEnumerator.hasNext()) {
                        Context c1 = contextEnumerator.next();
                        resState = this.getNextStates(action, body, acts, c1, s0, resState, nss, cm);
                    }
                }

                return resState;
            }
            case OPCODE_bf ->     // BoundedForall
            {
                final SemanticNode body = args[0];
                final IContextEnumerator contextEnumerator = this.contexts(pred, c, s0, s1, EvalControl.Clear, cm);

                if (!contextEnumerator.hasNext()) {
                    resState = this.getNextStates(action, acts, s0, s1, nss, cm);
                } else {
                    final Context c1 = contextEnumerator.next();

                    ActionItemList acts1 = acts;

                    while (contextEnumerator.hasNext()) {
                        Context c2 = contextEnumerator.next();
                        acts1 = (ActionItemList) acts1.cons(body, c2, cm, IActionItemList.PRED);
                    }
                    resState = this.getNextStates(action, body, acts1, c1, s0, s1, nss, cm);
                }
                return resState;
            }
            case OPCODE_fa ->     // FcnApply
            {
                Value fval = this.eval(args[0], c, s0, s1, EvalControl.KeepLazy, cm);
                if (fval instanceof final FcnLambdaValue fcn) {
                    if (fcn.fcnRcd == null) {
                        final Context c1 = this.getFcnContext(fcn, args, c, s0, s1, EvalControl.Clear, cm);
                        return this.getNextStates(action, fcn.body, acts, c1, s0, s1, nss, fcn.cm);
                    }
                    fval = fcn.fcnRcd;
                }
                if (!(fval instanceof Applicable)) {
                    Assert.fail("In computing next states, a non-function (" +
                            fval.getKindString() + ") was applied as a function.\n" + pred, pred, c);
                }
                final Applicable fcn = (Applicable) fval;
                final Value argVal = this.eval(args[1], c, s0, s1, EvalControl.Clear, cm);
                final Value bval = fcn.apply(argVal, EvalControl.Clear);
                if (!(bval instanceof BoolValue)) {
                    Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING2, new String[]{"next states", "boolean",
                            Objects.requireNonNull(pred).toString()}, args[1], c);
                }
                if (((BoolValue) bval).val) {
                    return this.getNextStates(action, acts, s0, s1, nss, cm);
                }
                return resState;
            }
            case OPCODE_aa ->     // AngleAct <A>_e
            {
                final ActionItemList acts1 = (ActionItemList) acts.cons(args[1], c, cm, IActionItemList.CHANGED);
                return this.getNextStates(action, args[0], acts1, c, s0, s1, nss, cm);
            }
            case OPCODE_sa ->     // [A]_e
            {
                /* The following two lines of code did not work, and were changed by
                 * YuanYu to mimic the way \/ works.  Change made
                 *  11 Mar 2009, with LL sitting next to him.
                 */
                resState = this.getNextStates(action, args[0], acts, c, s0, resState, nss, cm);
                return this.processUnchanged(action, args[1], acts, c, s0, resState, nss, cm);
            }
            case OPCODE_ite ->    // IfThenElse
            {
                final Value guard = this.eval(args[0], c, s0, s1, EvalControl.Clear, cm);
                if (!(guard instanceof BoolValue)) {
                    Assert.fail("In computing next states, a non-boolean expression (" +
                            guard.getKindString() + ") was used as the condition of" +
                            " an IF." + pred, pred, c);
                }
                if (((BoolValue) guard).val) {
                    return this.getNextStates(action, args[1], acts, c, s0, s1, nss, cm);
                } else {
                    return this.getNextStates(action, args[2], acts, c, s0, s1, nss, cm);
                }
            }
            case OPCODE_case ->   // Case
            {
                SemanticNode other = null;
                if (PROBABLISTIC) {
                    // See Bounded exists above!
                    throw new UnsupportedOperationException(
                            "Probabilistic evaluation of next-state relation not implemented for CASE yet.");
                }
                for (int i = 0; i < alen; i++) {
                    final OpApplNode pair = (OpApplNode) args[i];
                    final ExprOrOpArgNode[] pairArgs = pair.getArgs();
                    if (pairArgs[0] == null) {
                        other = pairArgs[1];
                    } else {
                        final Value bval = this.eval(pairArgs[0], c, s0, s1, EvalControl.Clear, coverage ? cm.get(args[i]) : cm);
                        if (!(bval instanceof BoolValue)) {
                            Assert.fail("In computing next states, a non-boolean expression (" +
                                    bval.getKindString() + ") was used as a guard condition" +
                                    " of a CASE.\n" + pairArgs[1], pairArgs[1], c);
                        }
                        if (((BoolValue) bval).val) {
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
            case OPCODE_eq -> {
                final SymbolNode var = this.getPrimedVar(args[0], c, false);
                // Assert.check(var.getName().getVarLoc() >= 0);
                if (var == null) {
                    final Value bval = this.eval(pred, c, s0, s1, EvalControl.Clear, cm);
                    if (!((BoolValue) bval).val) {
                        return resState;
                    }
                } else {
                    final UniqueString varName = var.getName();
                    final IValue lval = s1.lookup(varName);
                    final Value rval = this.eval(args[1], c, s0, s1, EvalControl.Clear, cm);
                    if (lval == null) {
                        resState.bind(varName, rval);
                        resState = this.getNextStates(action, acts, s0, resState, nss, cm);
                        resState.unbind(varName);
                        return resState;
                    } else if (!lval.equals(rval)) {
                        return resState;
                    }
                }
                return this.getNextStates(action, acts, s0, s1, nss, cm);
            }
            case OPCODE_in -> {
                final SymbolNode var = this.getPrimedVar(args[0], c, false);
                // Assert.check(var.getName().getVarLoc() >= 0);
                if (var == null) {
                    final Value bval = this.eval(pred, c, s0, s1, EvalControl.Clear, cm);
                    if (!((BoolValue) bval).val) {
                        return resState;
                    }
                } else {
                    final UniqueString varName = var.getName();
                    final Value lval = (Value) s1.lookup(varName);
                    final Value rval = this.eval(args[1], c, s0, s1, EvalControl.Clear, cm);
                    if (lval == null) {
                        if (!(rval instanceof Enumerable)) {
                            Assert.fail("In computing next states, the right side of \\IN" +
                                    " is not enumerable.\n" + pred, pred, c);
                        }

                        if (PROBABLISTIC) {
                            final ValueEnumeration Enum = ((Enumerable) rval).elements(Ordering.RANDOMIZED);
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

                        final ValueEnumeration Enum = ((Enumerable) rval).elements();
                        Value elem;
                        while ((elem = Enum.nextElement()) != null) {
                            resState.bind(varName, elem);
                            resState = this.getNextStates(action, acts, s0, resState, nss, cm);
                            resState.unbind(varName);
                        }
                        return resState;
                    } else if (!rval.member(lval)) {
                        return resState;
                    }
                }
                return this.getNextStates(action, acts, s0, s1, nss, cm);
            }
            case OPCODE_implies -> {
                final Value bval = this.eval(args[0], c, s0, s1, EvalControl.Clear, cm);
                if (!(bval instanceof BoolValue)) {
                    Assert.fail("In computing next states of a predicate of the form" +
                            " P => Q, P was\n" + bval.getKindString() + ".\n" + pred, pred, c);
                }
                if (((BoolValue) bval).val) {
                    return this.getNextStates(action, args[1], acts, c, s0, s1, nss, cm);
                } else {
                    return this.getNextStates(action, acts, s0, s1, nss, cm);
                }
            }
            case OPCODE_unchanged -> {
                return this.processUnchanged(action, args[0], acts, c, s0, s1, nss, cm);
            }
            case OPCODE_cdot -> {
                Assert.fail("The current version of TLC does not support action composition.", pred, c);
                /***
                 TLCState s01 = TLCStateFun.Empty;
                 StateVec iss = new StateVec(0);
                 this.getNextStates(action, args[0], ActionItemList.Empty, c, s0, s01, iss);
                 int sz = iss.size();
                 for (int i = 0; i < sz; i++) {
                 s01 = iss.get(i);
                 this.getNextStates(action, args[1], acts, c, s01, s1, nss);
                 }
                 ***/
                return s1;
            }

            // The following case added by LL on 13 Nov 2009 to handle subexpression names.
            case OPCODE_nop -> {
                return this.getNextStates(action, args[0], acts, c, s0, s1, nss, cm);
            }
            default -> {
                // We handle all the other builtin operators here.
                final Value bval = this.eval(pred, c, s0, s1, EvalControl.Clear, cm);
                if (!(bval instanceof BoolValue)) {
                    Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[]{"next states", "boolean",
                            bval.toString(), pred.toString()}, pred, c);
                }
                if (((BoolValue) bval).val) {
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

    protected final TLCState processUnchangedImpl(final Action action, final SemanticNode expr, final ActionItemList acts, final Context c,
                                                  final TLCState s0, final TLCState s1, final INextStateFunctor nss, CostModel cm) {
        if (coverage) {
            cm = cm.get(expr);
        }
        final SymbolNode var = this.getVar(expr, c, false, toolId);
        TLCState resState = s1;
        if (var != null) {
            return processUnchangedImplVar(action, expr, acts, s0, s1, nss, var, cm);
        }

        if (expr instanceof final OpApplNode expr1) {
            final ExprOrOpArgNode[] args = expr1.getArgs();
            final int alen = args.length;
            final SymbolNode opNode = expr1.getOperator();
            final UniqueString opName = opNode.getName();
            final int opcode = BuiltInOPs.getOpCode(opName);

            if (opcode == OPCODE_tup) {
                return processUnchangedImplTuple(action, acts, c, s0, s1, nss, args, alen, cm, coverage ? cm.get(expr1) : cm);
            }

            if (opcode == 0 && alen == 0) {
                // a 0-arity operator:
                return processUnchangedImpl0Arity(action, expr, acts, c, s0, s1, nss, cm, opNode, opName);
            }
        }

        final IValue v0 = this.eval(expr, c, s0, cm);
        final Value v1 = this.eval(expr, c, s1, TLCState.Null, EvalControl.Clear, cm);
        if (v0.equals(v1)) {
            resState = this.getNextStates(action, acts, s0, s1, nss, cm);
        }
        return resState;
    }

    @ExpectInlined
    private TLCState processUnchangedImpl0Arity(final Action action, final SemanticNode expr, final ActionItemList acts,
                                                final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss, final CostModel cm,
                                                final SymbolNode opNode, final UniqueString opName) {
        final Object val = this.lookup(opNode, c, false);

        if (val instanceof OpDefNode odn) {
            return this.processUnchanged(action, odn.getBody(), acts, c, s0, s1, nss, cm);
        } else if (val instanceof final LazyValue lv) {
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
    public IValue eval(final SemanticNode expr, final Context c, final TLCState s0) {
        return this.eval(expr, c, s0, EmptyState, EvalControl.Clear, CostModel.DO_NOT_RECORD);
    }

    @Override
    public IValue eval(final SemanticNode expr, final Context c) {
        return this.eval(expr, c, EmptyState);
    }

    @Override
    public IValue eval(final SemanticNode expr) {
        return this.eval(expr, Context.Empty);
    }

    @ExpectInlined
    private TLCState processUnchangedImplTuple(final Action action, final ActionItemList acts, final Context c, final TLCState s0, final TLCState s1, final INextStateFunctor nss,
                                               final ExprOrOpArgNode[] args, final int alen, final CostModel cm, final CostModel cmNested) {
        // a tuple:
        if (alen != 0) {
            ActionItemList acts1 = acts;
            for (int i = alen - 1; i > 0; i--) {
                acts1 = (ActionItemList) acts1.cons(args[i], c, cmNested, IActionItemList.UNCHANGED);
            }
            return this.processUnchanged(action, args[0], acts1, c, s0, s1, nss, cmNested);
        }
        return this.getNextStates(action, acts, s0, s1, nss, cm);
    }

    @ExpectInlined
    private TLCState processUnchangedImplVar(final Action action, final SemanticNode expr, final ActionItemList acts, final TLCState s0, final TLCState s1, final INextStateFunctor nss,
                                             final SymbolNode var, final CostModel cm) {
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
        } else if (val0.equals(val1)) {
            if (coverage) {
                resState = this.getNextStates(action, acts, s0, s1, nss, cm);
            } else {
                resState = this.getNextStates0(action, acts, s0, s1, nss, cm);
            }
        } else {
            MP.printWarning(EC.TLC_UNCHANGED_VARIABLE_CHANGED, varName.toString(), expr.toString());
        }
        return resState;
    }

    /* eval */
    @Override
    public TLCState evalAlias(final TLCState current, final TLCState successor) {
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
            final TLCState alias = eval(getAliasSpec(), Context.Empty, current, successor, EvalControl.Clear).toState(createEmptyState());
            if (alias != null) {
                return alias;
            }
        } catch (final EvalException | TLCRuntimeException e) {
            // Fall back to original state if eval fails.
            return current;
        }

        return current;
    }

    @Override
    public TLCStateInfo evalAlias(final TLCStateInfo current, final TLCState successor) {
        if ("".equals(this.config.getAlias())) {
            return current;
        }

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
            final TLCState alias = eval(getAliasSpec(), Context.Empty, current.state, successor, EvalControl.Clear).toState(createEmptyState());
            if (alias != null) {
                return new AliasTLCStateInfo(alias, current);
            }
        } catch (final EvalException | TLCRuntimeException e) {
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
    public IValue eval(final SemanticNode expr, final Context c, final TLCState s0, final CostModel cm) {
        return this.eval(expr, c, s0, EmptyState, EvalControl.Clear, cm);
    }

    @Override
    public final IValue eval(final SemanticNode expr, final Context c, final TLCState s0,
                             final TLCState s1, final int control) {
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
    @Override
    public abstract Value eval(SemanticNode expr, Context c, TLCState s0,
                               TLCState s1, final int control, final CostModel cm);

    @ExpectInlined
    protected Value evalImpl(final SemanticNode expr, final Context c, final TLCState s0,
                             final TLCState s1, final int control, CostModel cm) {
        switch (expr.getKind()) {
            /***********************************************************************
             * LabelKind class added by LL on 13 Jun 2007.                          *
             ***********************************************************************/
            case LabelKind -> {
                final LabelNode expr1 = (LabelNode) expr;
                return this.eval(expr1.getBody(), c, s0, s1, control, cm);
            }
            case OpApplKind -> {
                final OpApplNode expr1 = (OpApplNode) expr;
                if (coverage) {
                    cm = cm.get(expr);
                }
                return this.evalAppl(expr1, c, s0, s1, control, cm);
            }
            case LetInKind -> {
                return evalImplLetInKind((LetInNode) expr, c, s0, s1, control, cm);
            }
            case SubstInKind -> {
                return evalImplSubstInKind((SubstInNode) expr, c, s0, s1, control, cm);
            }

            // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
            case APSubstInKind -> {
                return evalImplApSubstInKind((APSubstInNode) expr, c, s0, s1, control, cm);
            }
            case NumeralKind, DecimalKind, StringKind -> {
                return (Value) WorkerValue.mux(expr.getToolObject(toolId));
            }
            case AtNodeKind -> {
                return (Value) c.lookup(EXCEPT_AT);
            }
            case OpArgKind -> {
                return evalImplOpArgKind((OpArgNode) expr, c, s0, s1, cm);
            }
            default -> {
                Assert.fail("Attempted to evaluate an expression that cannot be evaluated.\n" +
                        expr, expr, c);
                return null;     // make compiler happy
            }
        }
    }

    @ExpectInlined
    private Value evalImplLetInKind(final LetInNode expr1, final Context c, final TLCState s0, final TLCState s1, final int control, final CostModel cm) {
        final OpDefNode[] letDefs = expr1.getLets();

        Context c1 = c;
        for (final OpDefNode opDef : letDefs) {
            if (opDef.getArity() == 0) {
                final Value rhs = new LazyValue(opDef.getBody(), c1, cm);
                c1 = c1.cons(opDef, rhs);
            }
        }
        return this.eval(expr1.getBody(), c1, s0, s1, control, cm);
    }

    @ExpectInlined
    private Value evalImplSubstInKind(final SubstInNode expr1, final Context c, final TLCState s0, final TLCState s1, final int control, final CostModel cm) {
        final Subst[] subs = expr1.getSubsts();

        Context c1 = c;
        for (final Subst sub : subs) {
            c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true, coverage ? sub.getCM() : cm, toolId));
        }
        return this.eval(expr1.getBody(), c1, s0, s1, control, cm);
    }

    @ExpectInlined
    private Value evalImplApSubstInKind(final APSubstInNode expr1, final Context c, final TLCState s0, final TLCState s1, final int control, final CostModel cm) {
        final Subst[] subs = expr1.getSubsts();

        Context c1 = c;
        for (final Subst sub : subs) {
            c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true, cm, toolId));
        }
        return this.eval(expr1.getBody(), c1, s0, s1, control, cm);
    }

    @ExpectInlined
    private Value evalImplOpArgKind(final OpArgNode expr1, final Context c, final TLCState s0, final TLCState s1, final CostModel cm) {
        final SymbolNode opNode = expr1.getOp();
        final Object val = this.lookup(opNode, c, false);
        if (val instanceof OpDefNode odn) {
            return setSource(expr1, new OpLambdaValue(odn, this, c, s0, s1, cm));
        }
        return (Value) val;
    }

    /* evalAppl */

    @ExpectInlined
    protected abstract Value evalAppl(final OpApplNode expr, Context c, TLCState s0,
                                      TLCState s1, final int control, final CostModel cm);

    protected final Value evalApplImpl(final OpApplNode expr, final Context c, final TLCState s0,
                                       final TLCState s1, final int control, CostModel cm) {
        if (coverage) {
            cm = cm.getAndIncrement(expr);
        }
        final ExprOrOpArgNode[] args = expr.getArgs();
        final SymbolNode opNode = expr.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        if (opcode == 0) {
            // This is a user-defined operator with one exception: it may
            // be substed by a builtin operator. This special case occurs
            // when the lookup returns an OpDef with opcode # 0.
            Object val = this.lookup(opNode, c, s0, EvalControl.isPrimed(control));

            // First, unlazy if it is a lazy value. We cannot use the cached
            // value when s1 == null or isEnabled(control).
            if (val instanceof final LazyValue lv) {
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
            if (val instanceof final OpDefNode opDef) {
                opcode = BuiltInOPs.getOpCode(opDef.getName());
                if (opcode == 0) {
                    final Context c1 = this.getOpContext(opDef, args, c, true, cm, toolId);
                    res = this.eval(opDef.getBody(), c1, s0, s1, control, cm);
                }
            } else if (val instanceof Value v) {
                res = v;
                final int alen = args.length;
                if (alen == 0) {
                    if (val instanceof MethodValue mv) {
                        res = mv.apply(EmptyArgs, EvalControl.Clear);
                    } else if (val instanceof EvaluatingValue ev) {
                        // Allow EvaluatingValue overwrites to have zero arity.
                        res = ev.eval(this, args, c, s0, s1, control, cm);
                    }
                } else {
                    if (val instanceof OpValue ov) {
                        res = ov.eval(this, args, c, s0, s1, control, cm);
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
            else if (val instanceof final ThmOrAssumpDefNode opDef) {
                final Context c1 = this.getOpContext(opDef, args, c, true);
                return this.eval(opDef.getBody(), c1, s0, s1, control, cm);
            } else {
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
                            new String[]{opNode.getName().toString(), expr.toString()}, expr, c);
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
                        new String[]{opNode.getName().toString(), expr.toString()}, expr, c);
            }
            if (opcode == 0) {
                return res;
            }
        }

        switch (opcode) {

            case OPCODE_bc ->     // BoundedChoose
            {
                final SemanticNode pred = args[0];
                final SemanticNode inExpr = expr.getBdedQuantBounds()[0];
                final Value inVal = this.eval(inExpr, c, s0, s1, control, cm);
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

                final ValueEnumeration enumSet = ((Enumerable) inVal).elements(Ordering.NORMALIZED);
                final FormalParamNode[] bvars = expr.getBdedQuantSymbolLists()[0];
                final boolean isTuple = expr.isBdedQuantATuple()[0];
                if (isTuple) {
                    // Identifier tuple case:
                    final int cnt = bvars.length;
                    Value val;
                    while ((val = enumSet.nextElement()) != null) {
                        final TupleValue tv = (TupleValue) val.toTuple();
                        if (tv == null || tv.size() != cnt) {
                            Assert.fail("Attempted to compute the value of an expression of form\n" +
                                    "CHOOSE <<x1, ... , xN>> \\in S: P, but S was not a set\n" +
                                    "of N-tuples.\n" + expr, expr, c);
                        }
                        Context c1 = c;
                        for (int i = 0; i < cnt; i++) {
                            c1 = c1.cons(bvars[i], tv.elems[i]);
                        }
                        final Value bval = this.eval(pred, c1, s0, s1, control, cm);
                        if (!(bval instanceof BoolValue)) {
                            Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()}, pred, c1);
                        }
                        if (((BoolValue) bval).val) {
                            return val;
                        }
                    }
                } else {
                    // Simple identifier case:
                    final SymbolNode name = bvars[0];
                    Value val;
                    while ((val = enumSet.nextElement()) != null) {
                        final Context c1 = c.cons(name, val);
                        final Value bval = this.eval(pred, c1, s0, s1, control, cm);
                        if (!(bval instanceof BoolValue)) {
                            Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()}, pred, c1);
                        }
                        if (((BoolValue) bval).val) {
                            return val;
                        }
                    }
                }
                Assert.fail("Attempted to compute the value of an expression of form\n" +
                        "CHOOSE x \\in S: P, but no element of S satisfied P.\n" + expr, expr, c);
                return null;    // make compiler happy
            }
            case OPCODE_be ->     // BoundedExists
            {
                final IContextEnumerator contextEnumerator = this.contexts(expr, c, s0, s1, control, cm);
                final SemanticNode body = args[0];

                while (contextEnumerator.hasNext()) {
                    Context c1 = contextEnumerator.next();
                    final Value bval = this.eval(body, c1, s0, s1, control, cm);
                    if (!(bval instanceof BoolValue)) {
                        Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()}, body, c1);
                    }
                    if (((BoolValue) bval).val) {
                        return BoolValue.ValTrue;
                    }
                }
                return BoolValue.ValFalse;
            }
            case OPCODE_bf ->     // BoundedForall
            {
                final IContextEnumerator contextEnumerator = this.contexts(expr, c, s0, s1, control, cm);
                final SemanticNode body = args[0];

                while (contextEnumerator.hasNext()) {
                    Context c1 = contextEnumerator.next();
                    final Value bval = this.eval(body, c1, s0, s1, control, cm);
                    if (!(bval instanceof BoolValue)) {
                        Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()}, body, c1);
                    }
                    if (!((BoolValue) bval).val) {
                        return BoolValue.ValFalse;
                    }
                }
                return BoolValue.ValTrue;
            }
            case OPCODE_case ->   // Case
            {
                SemanticNode other = null;
                for (final ExprOrOpArgNode arg : args) {
                    final OpApplNode pairNode = (OpApplNode) arg;
                    final ExprOrOpArgNode[] pairArgs = pairNode.getArgs();
                    if (pairArgs[0] == null) {
                        other = pairArgs[1];
                        if (coverage) {
                            cm = cm.get(pairNode);
                        }
                    } else {
                        final Value bval = this.eval(pairArgs[0], c, s0, s1, control, coverage ? cm.get(pairNode) : cm);
                        if (!(bval instanceof BoolValue)) {
                            Assert.fail("A non-boolean expression (" + bval.getKindString() +
                                    ") was used as a condition of a CASE. " + pairArgs[0], pairArgs[0], c);
                        }
                        if (((BoolValue) bval).val) {
                            return this.eval(pairArgs[1], c, s0, s1, control, coverage ? cm.get(pairNode) : cm);
                        }
                    }
                }
                if (other == null) {
                    Assert.fail("Attempted to evaluate a CASE with no conditions true.\n" + expr, expr, c);
                }
                return this.eval(other, c, s0, s1, control, cm);
            }
            case OPCODE_cp ->     // CartesianProd
            {
                final int alen = args.length;
                final Value[] sets = new Value[alen];
                for (int i = 0; i < alen; i++) {
                    sets[i] = this.eval(args[i], c, s0, s1, control, cm);
                }
                return setSource(expr, new SetOfTuplesValue(sets, cm));
            }
            case OPCODE_cl ->     // ConjList
            {
                for (final ExprOrOpArgNode arg : args) {
                    final Value bval = this.eval(arg, c, s0, s1, control, cm);
                    if (!(bval instanceof BoolValue)) {
                        Assert.fail("A non-boolean expression (" + bval.getKindString() +
                                ") was used as a formula in a conjunction.\n" + arg, arg, c);
                    }
                    if (!((BoolValue) bval).val) {
                        return BoolValue.ValFalse;
                    }
                }
                return BoolValue.ValTrue;
            }
            case OPCODE_dl ->     // DisjList
            {
                for (final ExprOrOpArgNode arg : args) {
                    final Value bval = this.eval(arg, c, s0, s1, control, cm);
                    if (!(bval instanceof BoolValue)) {
                        Assert.fail("A non-boolean expression (" + bval.getKindString() +
                                ") was used as a formula in a disjunction.\n" + arg, arg, c);
                    }
                    if (((BoolValue) bval).val) {
                        return BoolValue.ValTrue;
                    }
                }
                return BoolValue.ValFalse;
            }
            case OPCODE_exc ->    // Except
            {
                final int alen = args.length;
                Value result = this.eval(args[0], c, s0, s1, control, cm);
                // SZ: variable not used ValueExcept[] expts = new ValueExcept[alen-1];
                for (int i = 1; i < alen; i++) {
                    final OpApplNode pairNode = (OpApplNode) args[i];
                    final ExprOrOpArgNode[] pairArgs = pairNode.getArgs();
                    final SemanticNode[] cmpts = ((OpApplNode) pairArgs[0]).getArgs();

                    final Value[] lhs = new Value[cmpts.length];
                    for (int j = 0; j < lhs.length; j++) {
                        lhs[j] = this.eval(cmpts[j], c, s0, s1, control, coverage ? cm.get(pairNode).get(pairArgs[0]) : cm);
                    }
                    final Value atVal = result.select(lhs);
                    if (atVal == null) {
                        // Do nothing but warn:
                        MP.printWarning(EC.TLC_EXCEPT_APPLIED_TO_UNKNOWN_FIELD, new String[]{args[0].toString()});
                    } else {
                        final Context c1 = c.cons(EXCEPT_AT, atVal);
                        final Value rhs = this.eval(pairArgs[1], c1, s0, s1, control, coverage ? cm.get(pairNode) : cm);
                        final ValueExcept vex = new ValueExcept(lhs, rhs);
                        result = result.takeExcept(vex);
                    }
                }
                return result;
            }
            case OPCODE_fa ->     // FcnApply
            {
                Value result = null;
                final Value fval = this.eval(args[0], c, s0, s1, EvalControl.setKeepLazy(control), cm);
                if ((fval instanceof FcnRcdValue) ||
                        (fval instanceof FcnLambdaValue)) {
                    final Applicable fcn = (Applicable) fval;
                    final Value argVal = this.eval(args[1], c, s0, s1, control, cm);
                    result = fcn.apply(argVal, control);
                } else if ((fval instanceof TupleValue) ||
                        (fval instanceof RecordValue)) {
                    final Applicable fcn = (Applicable) fval;
                    if (args.length != 2) {
                        Assert.fail("Attempted to evaluate an expression of form f[e1, ... , eN]" +
                                "\nwith f a tuple or record and N > 1.\n" + expr, expr, c);
                    }
                    final Value aval = this.eval(args[1], c, s0, s1, control, cm);
                    result = fcn.apply(aval, control);
                } else {
                    Assert.fail("A non-function (" + fval.getKindString() + ") was applied" +
                            " as a function.\n" + expr, expr, c);
                }
                return result;
            }
            // FcnConstructor
            // NonRecursiveFcnSpec
            case OPCODE_fc, OPCODE_nrfs, OPCODE_rfs ->    // RecursiveFcnSpec
            {
                final FormalParamNode[][] formals = expr.getBdedQuantSymbolLists();
                final boolean[] isTuples = expr.isBdedQuantATuple();
                final ExprNode[] domains = expr.getBdedQuantBounds();

                final Value[] dvals = new Value[domains.length];
                boolean isFcnRcd = true;
                for (int i = 0; i < dvals.length; i++) {
                    dvals[i] = this.eval(domains[i], c, s0, s1, control, cm);
                    isFcnRcd = isFcnRcd && (dvals[i] instanceof Reducible);
                }
                final FcnParams params = new FcnParams(formals, isTuples, dvals);

                final SemanticNode fbody = args[0];
                final FcnLambdaValue fval = (FcnLambdaValue) setSource(expr, new FcnLambdaValue(params, fbody, this, c, s0, s1, control, cm));
                if (opcode == OPCODE_rfs) {
                    final SymbolNode fname = expr.getUnbdedQuantSymbols()[0];
                    fval.makeRecursive(fname);
                    isFcnRcd = false;
                }
                if (isFcnRcd && !EvalControl.isKeepLazy(control)) {
                    return fval.toFcnRcd();
                }
                return fval;
            }
            case OPCODE_ite ->    // IfThenElse
            {
                final Value bval = this.eval(args[0], c, s0, s1, control, cm);
                if (!(bval instanceof BoolValue)) {
                    Assert.fail("A non-boolean expression (" + bval.getKindString() +
                            ") was used as the condition of an IF.\n" + expr, expr, c);
                }
                if (((BoolValue) bval).val) {
                    return this.eval(args[1], c, s0, s1, control, cm);
                }
                return this.eval(args[2], c, s0, s1, control, cm);
            }
            case OPCODE_rc ->     // RcdConstructor
            {
                final int alen = args.length;
                final UniqueString[] names = new UniqueString[alen];
                final Value[] vals = new Value[alen];
                for (int i = 0; i < alen; i++) {
                    final OpApplNode pairNode = (OpApplNode) args[i];
                    final ExprOrOpArgNode[] pair = pairNode.getArgs();
                    names[i] = ((StringValue) Objects.requireNonNull(pair[0].getToolObject(toolId))).getVal();
                    vals[i] = this.eval(pair[1], c, s0, s1, control, coverage ? cm.get(pairNode) : cm);
                }
                return setSource(expr, new RecordValue(names, vals, false, cm));
            }
            case OPCODE_rs ->     // RcdSelect
            {
                final Value rval = this.eval(args[0], c, s0, s1, control, cm);
                final Value sval = (Value) WorkerValue.mux(args[1].getToolObject(toolId));
                if (rval instanceof RecordValue rv) {
                    final Value result = rv.select(sval);
                    if (result == null) {
                        Assert.fail("Attempted to select nonexistent field " + sval + " from the" +
                                " record\n" + Values.ppr(rval.toString()) + "\n" + expr, expr, c);
                    }
                    return result;
                } else {
                    final FcnRcdValue fcn = (FcnRcdValue) rval.toFcnRcd();
                    if (fcn == null) {
                        Assert.fail("Attempted to select field " + sval + " from a non-record" +
                                " value " + Values.ppr(rval.toString()) + "\n" + expr, expr, c);
                    }
                    return fcn.apply(sval, control);
                }
            }
            case OPCODE_se ->     // SetEnumerate
            {
                final int alen = args.length;
                final ValueVec vals = new ValueVec(alen);
                for (final ExprOrOpArgNode arg : args) {
                    vals.add(this.eval(arg, c, s0, s1, control, cm));
                }
                return setSource(expr, new SetEnumValue(vals, false, cm));
            }
            case OPCODE_soa ->    // SetOfAll: {e(x) : x \in S}
            {
                final ValueVec vals = new ValueVec();
                final IContextEnumerator contextEnumerator = this.contexts(expr, c, s0, s1, control, cm);
                final SemanticNode body = args[0];

                while (contextEnumerator.hasNext()) {
                    Context c1 = contextEnumerator.next();
                    final Value val = this.eval(body, c1, s0, s1, control, cm);
                    vals.add(val);
                    // vals.addElement1(val);
                }
                return setSource(expr, new SetEnumValue(vals, false, cm));
            }
            case OPCODE_sor ->    // SetOfRcds
            {
                final int alen = args.length;
                final UniqueString[] names = new UniqueString[alen];
                final Value[] vals = new Value[alen];
                for (int i = 0; i < alen; i++) {
                    final OpApplNode pairNode = (OpApplNode) args[i];
                    final ExprOrOpArgNode[] pair = pairNode.getArgs();
                    names[i] = ((StringValue) Objects.requireNonNull(pair[0].getToolObject(toolId))).getVal();
                    vals[i] = this.eval(pair[1], c, s0, s1, control, coverage ? cm.get(pairNode) : cm);
                }
                return setSource(expr, new SetOfRcdsValue(names, vals, false, cm));
            }
            case OPCODE_sof ->    // SetOfFcns
            {
                final Value lhs = this.eval(args[0], c, s0, s1, control, cm);
                final Value rhs = this.eval(args[1], c, s0, s1, control, cm);
                return setSource(expr, new SetOfFcnsValue(lhs, rhs, cm));
            }
            case OPCODE_sso ->    // SubsetOf
            {
                final SemanticNode pred = args[0];
                final SemanticNode inExpr = expr.getBdedQuantBounds()[0];
                final Value inVal = this.eval(inExpr, c, s0, s1, control, cm);
                final boolean isTuple = expr.isBdedQuantATuple()[0];
                final FormalParamNode[] bvars = expr.getBdedQuantSymbolLists()[0];
                if (inVal instanceof Reducible) {
                    final ValueVec vals = new ValueVec();
                    final ValueEnumeration enumSet = ((Enumerable) inVal).elements();
                    Value elem;
                    if (isTuple) {
                        while ((elem = enumSet.nextElement()) != null) {
                            Context c1 = c;
                            final Value[] tuple = ((TupleValue) elem).elems;
                            for (int i = 0; i < bvars.length; i++) {
                                c1 = c1.cons(bvars[i], tuple[i]);
                            }
                            final Value bval = this.eval(pred, c1, s0, s1, control, cm);
                            if (!(bval instanceof BoolValue)) {
                                Assert.fail("Attempted to evaluate an expression of form {x \\in S : P(x)}" +
                                        " when P was " + bval.getKindString() + ".\n" + pred, pred, c1);
                            }
                            if (((BoolValue) bval).val) {
                                vals.add(elem);
                            }
                        }
                    } else {
                        final SymbolNode idName = bvars[0];
                        while ((elem = enumSet.nextElement()) != null) {
                            final Context c1 = c.cons(idName, elem);
                            final Value bval = this.eval(pred, c1, s0, s1, control, cm);
                            if (!(bval instanceof BoolValue)) {
                                Assert.fail("Attempted to evaluate an expression of form {x \\in S : P(x)}" +
                                        " when P was " + bval.getKindString() + ".\n" + pred, pred, c1);
                            }
                            if (((BoolValue) bval).val) {
                                vals.add(elem);
                            }
                        }
                    }
                    return setSource(expr, new SetEnumValue(vals, inVal.isNormalized(), cm));
                } else if (isTuple) {
                    return setSource(expr, new SetPredValue(bvars, inVal, pred, this, c, s0, s1, control, cm));
                } else {
                    return setSource(expr, new SetPredValue(bvars[0], inVal, pred, this, c, s0, s1, control, cm));
                }
            }
            case OPCODE_tup ->    // Tuple
            {
                final int alen = args.length;
                final Value[] vals = new Value[alen];
                for (int i = 0; i < alen; i++) {
                    vals[i] = this.eval(args[i], c, s0, s1, control, cm);
                }
                return setSource(expr, new TupleValue(vals, cm));
            }
            case OPCODE_uc ->     // UnboundedChoose
            {
                Assert.fail("TLC attempted to evaluate an unbounded CHOOSE.\n" +
                        "Make sure that the expression is of form CHOOSE x \\in S: P(x).\n" +
                        expr, expr, c);
                return null;    // make compiler happy
            }
            case OPCODE_ue ->     // UnboundedExists
            {
                Assert.fail("TLC attempted to evaluate an unbounded \\E.\n" +
                        "Make sure that the expression is of form \\E x \\in S: P(x).\n" +
                        expr, expr, c);
                return null;    // make compiler happy
            }
            case OPCODE_uf ->     // UnboundedForall
            {
                Assert.fail("TLC attempted to evaluate an unbounded \\A.\n" +
                        "Make sure that the expression is of form \\A x \\in S: P(x).\n" +
                        expr, expr, c);
                return null;    // make compiler happy
            }
            case OPCODE_lnot -> {
                final Value arg = this.eval(args[0], c, s0, s1, control, cm);
                if (!(arg instanceof BoolValue)) {
                    Assert.fail("Attempted to apply the operator ~ to a non-boolean\n(" +
                            arg.getKindString() + ")\n" + expr, args[0], c);
                }
                return (((BoolValue) arg).val) ? BoolValue.ValFalse : BoolValue.ValTrue;
            }
            case OPCODE_subset -> {
                final Value arg = this.eval(args[0], c, s0, s1, control, cm);
                return setSource(expr, new SubsetValue(arg, cm));
            }
            case OPCODE_union -> {
                final Value arg = this.eval(args[0], c, s0, s1, control, cm);
                return setSource(expr, UnionValue.union(arg));
            }
            case OPCODE_domain -> {
                final Value arg = this.eval(args[0], c, s0, s1, control, cm);
                if (!(arg instanceof Applicable)) {
                    Assert.fail("Attempted to apply the operator DOMAIN to a non-function\n(" +
                            arg.getKindString() + ")\n" + expr, expr, c);
                }
                return setSource(expr, ((Applicable) arg).getDomain());
            }
            case OPCODE_enabled -> {
                TLCState sfun = TLCStateFun.Empty;
                final Context c1 = Context.branch(c);
                sfun = this.enabled(args[0], ActionItemList.Empty.getEmpty(), c1, s0, sfun, cm);
                return (sfun != null) ? BoolValue.ValTrue : BoolValue.ValFalse;
            }
            case OPCODE_eq -> {
                final Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
                final Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
                return (arg1.equals(arg2)) ? BoolValue.ValTrue : BoolValue.ValFalse;
            }
            case OPCODE_land -> {
                final Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
                if (!(arg1 instanceof BoolValue)) {
                    Assert.fail("Attempted to evaluate an expression of form P /\\ Q" +
                            " when P was\n" + arg1.getKindString() + ".\n" + expr, expr, c);
                }
                if (((BoolValue) arg1).val) {
                    final Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
                    if (!(arg2 instanceof BoolValue)) {
                        Assert.fail("Attempted to evaluate an expression of form P /\\ Q" +
                                " when Q was\n" + arg2.getKindString() + ".\n" + expr, expr, c);
                    }
                    return arg2;
                }
                return BoolValue.ValFalse;
            }
            case OPCODE_lor -> {
                final Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
                if (!(arg1 instanceof BoolValue)) {
                    Assert.fail("Attempted to evaluate an expression of form P \\/ Q" +
                            " when P was\n" + arg1.getKindString() + ".\n" + expr, expr, c);
                }
                if (((BoolValue) arg1).val) {
                    return BoolValue.ValTrue;
                }
                final Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
                if (!(arg2 instanceof BoolValue)) {
                    Assert.fail("Attempted to evaluate an expression of form P \\/ Q" +
                            " when Q was\n" + arg2.getKindString() + ".\n" + expr, expr, c);
                }
                return arg2;
            }
            case OPCODE_implies -> {
                final Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
                if (!(arg1 instanceof BoolValue)) {
                    Assert.fail("Attempted to evaluate an expression of form P => Q" +
                            " when P was\n" + arg1.getKindString() + ".\n" + expr, expr, c);
                }
                if (((BoolValue) arg1).val) {
                    final Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
                    if (!(arg2 instanceof BoolValue)) {
                        Assert.fail("Attempted to evaluate an expression of form P => Q" +
                                " when Q was\n" + arg2.getKindString() + ".\n" + expr, expr, c);
                    }
                    return arg2;
                }
                return BoolValue.ValTrue;
            }
            case OPCODE_equiv -> {
                final Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
                final Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
                if (!(arg1 instanceof BoolValue) || !(arg2 instanceof BoolValue)) {
                    Assert.fail("Attempted to evaluate an expression of form P <=> Q" +
                            " when P or Q was not a boolean.\n" + expr, expr, c);
                }
                final BoolValue bval1 = (BoolValue) arg1;
                final BoolValue bval2 = (BoolValue) arg2;
                return (bval1.val == bval2.val) ? BoolValue.ValTrue : BoolValue.ValFalse;
            }
            case OPCODE_noteq -> {
                final Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
                final Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
                return arg1.equals(arg2) ? BoolValue.ValFalse : BoolValue.ValTrue;
            }
            case OPCODE_subseteq -> {
                final Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
                final Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
                if (!(arg1 instanceof Enumerable)) {
                    Assert.fail("Attempted to evaluate an expression of form S \\subseteq T," +
                            " but S was not enumerable.\n" + expr, expr, c);
                }
                return ((Enumerable) arg1).isSubsetEq(arg2);
            }
            case OPCODE_in -> {
                final Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
                final Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
                return (arg2.member(arg1)) ? BoolValue.ValTrue : BoolValue.ValFalse;
            }
            case OPCODE_notin -> {
                final Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
                final Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
                return (arg2.member(arg1)) ? BoolValue.ValFalse : BoolValue.ValTrue;
            }
            case OPCODE_setdiff -> {
                final Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
                final Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
                if (arg1 instanceof Reducible r) {
                    return setSource(expr, r.diff(arg2));
                }
                return setSource(expr, new SetDiffValue(arg1, arg2));
            }
            case OPCODE_cap -> {
                final Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
                final Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
                if (arg1 instanceof Reducible r) {
                    return setSource(expr, r.cap(arg2));
                } else if (arg2 instanceof Reducible r) {
                    return setSource(expr, r.cap(arg1));
                }
                return setSource(expr, new SetCapValue(arg1, arg2));
            }
            case OPCODE_nop ->
            // Added by LL on 2 Aug 2007
            {
                return eval(args[0], c, s0, s1, control, cm);
            }
            case OPCODE_cup -> {
                final Value arg1 = this.eval(args[0], c, s0, s1, control, cm);
                final Value arg2 = this.eval(args[1], c, s0, s1, control, cm);
                if (arg1 instanceof Reducible r) {
                    return setSource(expr, r.cup(arg2));
                } else if (arg2 instanceof Reducible r) {
                    return setSource(expr, r.cup(arg1));
                }
                return setSource(expr, new SetCupValue(arg1, arg2, cm));
            }
            case OPCODE_prime -> {
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
                return this.eval(args[0], c, s1, TLCState.Null, EvalControl.setPrimedIfEnabled(control), cm);
            }
            case OPCODE_unchanged -> {
                final Value v0 = this.eval(args[0], c, s0, EmptyState, control, cm);
                final Value v1 = this.eval(args[0], c, s1, TLCState.Null, EvalControl.setPrimedIfEnabled(control), cm);
                return (v0.equals(v1)) ? BoolValue.ValTrue : BoolValue.ValFalse;
            }
            case OPCODE_aa ->     // <A>_e
            {
                final Value res = this.eval(args[0], c, s0, s1, control, cm);
                if (!(res instanceof BoolValue)) {
                    Assert.fail("Attempted to evaluate an expression of form <A>_e," +
                            " but A was not a boolean.\n" + expr, expr, c);
                }
                if (!((BoolValue) res).val) {
                    return BoolValue.ValFalse;
                }
                final Value v0 = this.eval(args[1], c, s0, EmptyState, control, cm);
                final Value v1 = this.eval(args[1], c, s1, TLCState.Null, EvalControl.setPrimedIfEnabled(control), cm);
                return v0.equals(v1) ? BoolValue.ValFalse : BoolValue.ValTrue;
            }
            case OPCODE_sa ->     // [A]_e
            {
                final Value res = this.eval(args[0], c, s0, s1, control, cm);
                if (!(res instanceof BoolValue)) {
                    Assert.fail("Attempted to evaluate an expression of form [A]_e," +
                            " but A was not a boolean.\n" + expr, expr, c);
                }
                if (((BoolValue) res).val) {
                    return BoolValue.ValTrue;
                }
                final Value v0 = this.eval(args[1], c, s0, EmptyState, control, cm);
                final Value v1 = this.eval(args[1], c, s1, TLCState.Null, EvalControl.setPrimedIfEnabled(control), cm);
                return (v0.equals(v1)) ? BoolValue.ValTrue : BoolValue.ValFalse;
            }
            case OPCODE_cdot -> {
                Assert.fail("The current version of TLC does not support action composition.", expr, c);
                /***
                 TLCState s01 = TLCStateFun.Empty;
                 StateVec iss = new StateVec(0);
                 this.getNextStates(args[0], ActionItemList.Empty, c, s0, s01, iss);
                 int sz = iss.size();
                 for (int i = 0; i < sz; i++) {
                 s01 = iss.get(i);
                 this.eval(args[1], c, s01, s1, control);
                 }
                 ***/
                return null;    // make compiler happy
            }
            case OPCODE_sf ->     // SF
            {
                Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"SF", expr.toString()}, expr, c);
                return null;    // make compiler happy
            }
            case OPCODE_wf ->     // WF
            {
                Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"WF", expr.toString()}, expr, c);
                return null;    // make compiler happy
            }
            case OPCODE_te ->     // TemporalExists
            {
                Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"\\EE", expr.toString()}, expr, c);
                return null;    // make compiler happy
            }
            case OPCODE_tf ->     // TemporalForAll
            {
                Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"\\AA", expr.toString()}, expr, c);
                return null;    // make compiler happy
            }
            case OPCODE_leadto -> {
                Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"a ~> b", expr.toString()}, expr, c);
                return null;    // make compiler happy
            }
            case OPCODE_arrow -> {
                Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"a -+-> formula", expr.toString()}, expr, c);
                return null;    // make compiler happy
            }
            case OPCODE_box -> {
                Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"[]A", expr.toString()}, expr, c);
                return null;    // make compiler happy
            }
            case OPCODE_diamond -> {
                Assert.fail(EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE, new String[]{"<>A", expr.toString()}, expr, c);
                return null;    // make compiler happy
            }
            default -> {
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
    public final boolean isGoodState(final TLCState state) {
        return state.allAssigned();
    }

    /* This method determines if a state satisfies the model constraints. */
    @Override
    public final boolean isInModel(final TLCState state) throws EvalException {
        final ExprNode[] constrs = this.getModelConstraints();
        for (final ExprNode constr : constrs) {
            final CostModel cm = coverage ? ((Action) Objects.requireNonNull(constr.getToolObject(toolId))).cm : CostModel.DO_NOT_RECORD;
            final IValue bval = this.eval(constr, Context.Empty, state, cm);
            if (!(bval instanceof BoolValue)) {
                Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", constr.toString()}, constr);
            }
            if (!((BoolValue) bval).val) {
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
    public final boolean isInActions(final TLCState s1, final TLCState s2) throws EvalException {
        final ExprNode[] constrs = this.getActionConstraints();
        for (final ExprNode constr : constrs) {
            final CostModel cm = coverage ? ((Action) Objects.requireNonNull(constr.getToolObject(toolId))).cm : CostModel.DO_NOT_RECORD;
            final Value bval = this.eval(constr, Context.Empty, s1, s2, EvalControl.Clear, cm);
            if (!(bval instanceof BoolValue)) {
                Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", constr.toString()}, constr);
            }
            if (!((BoolValue) bval).val) {
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
    public final TLCState enabled(final SemanticNode pred, final Context c, final TLCState s0, final TLCState s1) {
        return enabled(pred, ActionItemList.Empty, c, s0, s1, CostModel.DO_NOT_RECORD);
    }

    @Override
    public final TLCState enabled(final SemanticNode pred, final Context c, final TLCState s0, final TLCState s1, final ExprNode subscript, final int ail) {
        final ActionItemList acts = (ActionItemList) ActionItemList.Empty.cons(subscript, c, CostModel.DO_NOT_RECORD, ail);
        return enabled(pred, acts, c, s0, s1, CostModel.DO_NOT_RECORD);
    }

    @Override
    public final TLCState enabled(final SemanticNode pred, final IActionItemList acts, final Context c, final TLCState s0, final TLCState s1) {
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

    protected final TLCState enabledImpl(final SemanticNode pred, final ActionItemList acts,
                                         final Context c, final TLCState s0, final TLCState s1, final CostModel cm) {
        switch (pred.getKind()) {
            case OpApplKind -> {
                final OpApplNode pred1 = (OpApplNode) pred;
                return this.enabledAppl(pred1, acts, c, s0, s1, cm);
            }
            case LetInKind -> {
                final LetInNode pred1 = (LetInNode) pred;
                final OpDefNode[] letDefs = pred1.getLets();
                Context c1 = c;
                for (final OpDefNode opDef : letDefs) {
                    if (opDef.getArity() == 0) {
                        final Value rhs = new LazyValue(opDef.getBody(), c1, cm);
                        c1 = c1.cons(opDef, rhs);
                    }
                }
                return this.enabled(pred1.getBody(), acts, c1, s0, s1, cm);
            }
            case SubstInKind -> {
                final SubstInNode pred1 = (SubstInNode) pred;
                final Subst[] subs = pred1.getSubsts();

                Context c1 = c;
                for (final Subst sub : subs) {
                    c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, coverage ? sub.getCM() : cm, toolId));
                }
                return this.enabled(pred1.getBody(), acts, c1, s0, s1, cm);
            }

            // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
            case APSubstInKind -> {
                final APSubstInNode pred1 = (APSubstInNode) pred;
                final Subst[] subs = pred1.getSubsts();

                Context c1 = c;
                for (final Subst sub : subs) {
                    c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, false, cm, toolId));
                }
                return this.enabled(pred1.getBody(), acts, c1, s0, s1, cm);
            }

            // LabelKind class added by LL on 13 Jun 2007
            case LabelKind -> {
                final LabelNode pred1 = (LabelNode) pred;
                return this.enabled(pred1.getBody(), acts, c, s0, s1, cm);
            }
            default -> {
                // We should not compute enabled on anything else.
                Assert.fail("Attempted to compute ENABLED on a non-boolean expression.\n" + pred, pred, c);
                return null;    // make compiler happy
            }
        }
    }

    private TLCState enabled(final ActionItemList acts, final TLCState s0, final TLCState s1, CostModel cm) {
        if (acts.isEmpty()) return s1;

        final int kind = acts.carKind();
        final SemanticNode pred = acts.carPred();
        final Context c = acts.carContext();
        cm = acts.cm;
        final ActionItemList acts1 = acts.cdr();
        if (kind > IActionItemList.CONJUNCT) {
            return this.enabled(pred, acts1, c, s0, s1, cm);
        } else if (kind == IActionItemList.PRED) {
            return this.enabled(pred, acts1, c, s0, s1, cm);
        }
        if (kind == IActionItemList.UNCHANGED) {
            return this.enabledUnchanged(pred, acts1, c, s0, s1, cm);
        }

        final Value v1 = this.eval(pred, c, s0, EmptyState, EvalControl.Enabled, cm);
        // We are now in ENABLED and primed state. Second TLCState parameter being null
        // effectively disables LazyValue in evalAppl (same effect as
        // EvalControl.setPrimed(EvalControl.Enabled)).
        final Value v2 = this.eval(pred, c, s1, TLCState.Null, EvalControl.Primed, cm);

        if (v1.equals(v2)) return null;
        return this.enabled(acts1, s0, s1, cm);
    }

    protected abstract TLCState enabledAppl(OpApplNode pred, ActionItemList acts, Context c, TLCState s0, TLCState s1, CostModel cm);

    protected final TLCState enabledApplImpl(final OpApplNode pred, final ActionItemList acts, final Context c, final TLCState s0, final TLCState s1, CostModel cm) {
        if (coverage) {
            cm = cm.get(pred);
        }
        final ExprOrOpArgNode[] args = pred.getArgs();
        final int alen = args.length;
        final SymbolNode opNode = pred.getOperator();
        int opcode = BuiltInOPs.getOpCode(opNode.getName());

        if (opcode == 0) {
            // This is a user-defined operator with one exception: it may
            // be substed by a builtin operator. This special case occurs
            // when the lookup returns an OpDef with opcode # 0.
            final Object val = this.lookup(opNode, c, s0, false);

            if (val instanceof final OpDefNode opDef) {
                opcode = BuiltInOPs.getOpCode(opDef.getName());
                if (opcode == 0) {
                    // Context c1 = this.getOpContext(opDef, args, c, false);
                    final Context c1 = this.getOpContext(opDef, args, c, true, cm, toolId);
                    return this.enabled(opDef.getBody(), acts, c1, s0, s1, cm);
                }
            }


            // Added 13 Nov 2009 by LL to handle theorem or assumption names
            /*********************************************************************
             * Modified on 23 October 2012 by LL to work if ThmOrAssumpDefNode    *
             * imported with parameterized instantiation.                         *
             *********************************************************************/
            if (val instanceof final ThmOrAssumpDefNode opDef) {
                final Context c1 = this.getOpContext(opDef, args, c, true);
                return this.enabled(opDef.getBody(), acts, c1, s0, s1, cm);
            }


            if (val instanceof final LazyValue lv) {
                return this.enabled(lv.expr, acts, lv.con, s0, s1, lv.cm);
            }

            Object bval = val;
            if (alen == 0) {
                if (val instanceof MethodValue mv) {
                    bval = mv.apply(EmptyArgs, EvalControl.Clear); // EvalControl.Clear is ignored by MethodValuea#apply
                } else if (val instanceof EvaluatingValue ev) {
                    bval = ev.eval(this, args, c, s0, s1, EvalControl.Enabled, cm);
                }
            } else {
                if (val instanceof OpValue ov) {
                    bval = ov.eval(this, args, c, s0, s1, EvalControl.Enabled, cm);
                }
            }

            if (opcode == 0) {
                if (!(bval instanceof BoolValue)) {
                    Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[]{"ENABLED", "boolean",
                            bval.toString(), pred.toString()}, pred, c);
                }
                if (((BoolValue) bval).val) {
                    return this.enabled(acts, s0, s1, cm);
                }
                return null;
            }
        }

        switch (opcode) {
            case OPCODE_aa -> // AngleAct <A>_e
            {
                final ActionItemList acts1 = (ActionItemList) acts.cons(args[1], c, cm, IActionItemList.CHANGED);
                return this.enabled(args[0], acts1, c, s0, s1, cm);
            }
            case OPCODE_be -> // BoundedExists
            {
                final SemanticNode body = args[0];
                final IContextEnumerator contextEnumerator = this.contexts(pred, c, s0, s1, EvalControl.Enabled, cm);

                while (contextEnumerator.hasNext()) {
                    Context c1 = contextEnumerator.next();
                    final TLCState s2 = this.enabled(body, acts, c1, s0, s1, cm);
                    if (s2 != null) {
                        return s2;
                    }
                }
                return null;
            }
            case OPCODE_bf -> // BoundedForall
            {
                final SemanticNode body = args[0];
                final IContextEnumerator contextEnumerator = this.contexts(pred, c, s0, s1, EvalControl.Enabled, cm);

                if (!contextEnumerator.hasNext()) {
                    return this.enabled(acts, s0, s1, cm);
                }

                final Context c1 = contextEnumerator.next();

                ActionItemList acts1 = acts;

                while (contextEnumerator.hasNext()) {
                    Context c2 = contextEnumerator.next();
                    acts1 = (ActionItemList) acts1.cons(body, c2, cm, IActionItemList.PRED);
                }
                return this.enabled(body, acts1, c1, s0, s1, cm);
            }
            case OPCODE_case -> // Case
            {
                SemanticNode other = null;
                for (final ExprOrOpArgNode arg : args) {
                    final OpApplNode pair = (OpApplNode) arg;
                    final ExprOrOpArgNode[] pairArgs = pair.getArgs();
                    if (pairArgs[0] == null) {
                        other = pairArgs[1];
                    } else {
                        final Value bval = this.eval(pairArgs[0], c, s0, s1, EvalControl.Enabled, cm);
                        if (!(bval instanceof BoolValue)) {
                            Assert.fail("In computing ENABLED, a non-boolean expression(" + bval.getKindString()
                                    + ") was used as a guard condition" + " of a CASE.\n" + pairArgs[1], pairArgs[1], c);
                        }
                        if (((BoolValue) bval).val) {
                            return this.enabled(pairArgs[1], acts, c, s0, s1, cm);
                        }
                    }
                }
                if (other == null) {
                    Assert.fail("In computing ENABLED, TLC encountered a CASE with no" + " conditions true.\n" + pred, pred, c);
                }
                return this.enabled(other, acts, c, s0, s1, cm);
            }
            // ConjList
            case OPCODE_cl, OPCODE_land -> {
                ActionItemList acts1 = acts;
                for (int i = alen - 1; i > 0; i--) {
                    acts1 = (ActionItemList) acts1.cons(args[i], c, cm, i);
                }
                return this.enabled(args[0], acts1, c, s0, s1, cm);
            }
            // DisjList
            case OPCODE_dl, OPCODE_lor -> {
                for (final ExprOrOpArgNode arg : args) {
                    final TLCState s2 = this.enabled(arg, acts, c, s0, s1, cm);
                    if (s2 != null) {
                        return s2;
                    }
                }
                return null;
            }
            case OPCODE_fa -> // FcnApply
            {
                Value fval = this.eval(args[0], c, s0, s1, EvalControl.setKeepLazy(EvalControl.Enabled), cm); // KeepLazy does not interfere with EvalControl.Enabled in this.evalAppl
                if (fval instanceof final FcnLambdaValue fcn) {
                    if (fcn.fcnRcd == null) {
                        final Context c1 = this.getFcnContext(fcn, args, c, s0, s1, EvalControl.Enabled, cm); // EvalControl.Enabled passed on to nested this.evalAppl
                        return this.enabled(fcn.body, acts, c1, s0, s1, cm);
                    }
                    fval = fcn.fcnRcd;
                }
                if (fval instanceof final Applicable fcn) {
                    final Value argVal = this.eval(args[1], c, s0, s1, EvalControl.Enabled, cm);
                    final Value bval = fcn.apply(argVal, EvalControl.Enabled); // EvalControl.Enabled not taken into account by any subclass of Applicable
                    if (!(bval instanceof BoolValue)) {
                        Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING2, new String[]{"ENABLED", "boolean",
                                pred.toString()}, args[1], c);
                    }
                    if (!((BoolValue) bval).val) {
                        return null;
                    }
                } else {
                    Assert.fail("In computing ENABLED, a non-function (" + fval.getKindString()
                            + ") was applied as a function.\n" + pred, pred, c);
                }
                return this.enabled(acts, s0, s1, cm);
            }
            case OPCODE_ite -> // IfThenElse
            {
                final Value guard = this.eval(args[0], c, s0, s1, EvalControl.Enabled, cm);
                if (!(guard instanceof BoolValue)) {
                    Assert.fail("In computing ENABLED, a non-boolean expression(" + guard.getKindString()
                            + ") was used as the guard condition" + " of an IF.\n" + pred, pred, c);
                }
                final int idx = (((BoolValue) guard).val) ? 1 : 2;
                return this.enabled(args[idx], acts, c, s0, s1, cm);
            }
            case OPCODE_sa -> // SquareAct [A]_e
            {
                final TLCState s2 = this.enabled(args[0], acts, c, s0, s1, cm);
                if (s2 != null) {
                    return s2;
                }
                return this.enabledUnchanged(args[1], acts, c, s0, s1, cm);
            }
            // TemporalExists
            case OPCODE_te, OPCODE_tf -> // TemporalForAll
            {
                Assert.fail("In computing ENABLED, TLC encountered temporal quantifier.\n" + pred, pred, c);
                return null; // make compiler happy
            }
            case OPCODE_uc -> // UnboundedChoose
            {
                Assert.fail("In computing ENABLED, TLC encountered unbounded CHOOSE. "
                        + "Make sure that the expression is of form CHOOSE x \\in S: P(x).\n" + pred, pred, c);
                return null; // make compiler happy
            }
            case OPCODE_ue -> // UnboundedExists
            {
                Assert.fail("In computing ENABLED, TLC encountered unbounded quantifier. "
                        + "Make sure that the expression is of form \\E x \\in S: P(x).\n" + pred, pred, c);
                return null; // make compiler happy
            }
            case OPCODE_uf -> // UnboundedForall
            {
                Assert.fail("In computing ENABLED, TLC encountered unbounded quantifier. "
                        + "Make sure that the expression is of form \\A x \\in S: P(x).\n" + pred, pred, c);
                return null; // make compiler happy
            }
            case OPCODE_sf -> // SF
            {
                Assert.fail(EC.TLC_ENABLED_WRONG_FORMULA, new String[]{"SF", pred.toString()}, pred, c);
                return null; // make compiler happy
            }
            case OPCODE_wf -> // WF
            {
                Assert.fail(EC.TLC_ENABLED_WRONG_FORMULA, new String[]{"WF", pred.toString()}, pred, c);
                return null; // make compiler happy
            }
            case OPCODE_box -> {
                Assert.fail(EC.TLC_ENABLED_WRONG_FORMULA, new String[]{"[]", pred.toString()}, pred, c);
                return null; // make compiler happy
            }
            case OPCODE_diamond -> {
                Assert.fail(EC.TLC_ENABLED_WRONG_FORMULA, new String[]{"<>", pred.toString()}, pred, c);
                return null; // make compiler happy
            }
            case OPCODE_unchanged -> {
                return this.enabledUnchanged(args[0], acts, c, s0, s1, cm);
            }
            case OPCODE_eq -> {
                final SymbolNode var = this.getPrimedVar(args[0], c, true);
                if (var == null) {
                    final Value bval = this.eval(pred, c, s0, s1, EvalControl.Enabled, cm);
                    if (!((BoolValue) bval).val) {
                        return null;
                    }
                } else {
                    final UniqueString varName = var.getName();
                    final IValue lval = s1.lookup(varName);
                    final Value rval = this.eval(args[1], c, s0, s1, EvalControl.Enabled, cm);
                    if (lval == null) {
                        final TLCState s2 = s1.bind(var, rval);
                        return this.enabled(acts, s0, s2, cm);
                    } else {
                        if (!lval.equals(rval)) {
                            return null;
                        }
                    }
                }
                return this.enabled(acts, s0, s1, cm);
            }
            case OPCODE_implies -> {
                final Value bval = this.eval(args[0], c, s0, s1, EvalControl.Enabled, cm);
                if (!(bval instanceof BoolValue)) {
                    Assert.fail("While computing ENABLED of an expression of the form" + " P => Q, P was "
                            + bval.getKindString() + ".\n" + pred, pred, c);
                }
                if (((BoolValue) bval).val) {
                    return this.enabled(args[1], acts, c, s0, s1, cm);
                }
                return this.enabled(acts, s0, s1, cm);
            }
            case OPCODE_cdot -> {
                Assert.fail("The current version of TLC does not support action composition.", pred, c);
                /***
                 TLCState s01 = TLCStateFun.Empty;
                 StateVec iss = new StateVec(0);
                 this.getNextStates(args[0], ActionItemList.Empty, c, s0, s01, iss);
                 int sz = iss.size();
                 for (int i = 0; i < sz; i++) {
                 s01 = iss.get(i);
                 TLCState s2 = this.enabled(args[1], acts, c, s01, s1);
                 if (s2 != null) return s2;
                 }
                 ***/
                return null; // make compiler happy
            }
            case OPCODE_leadto -> {
                Assert.fail("In computing ENABLED, TLC encountered a temporal formula" + " (a ~> b).\n" + pred, pred, c);
                return null; // make compiler happy
            }
            case OPCODE_arrow -> {
                Assert.fail("In computing ENABLED, TLC encountered a temporal formula" + " (a -+-> formula).\n" + pred, pred, c);
                return null; // make compiler happy
            }
            case OPCODE_in -> {
                final SymbolNode var = this.getPrimedVar(args[0], c, true);
                if (var == null) {
                    final Value bval = this.eval(pred, c, s0, s1, EvalControl.Enabled, cm);
                    if (!((BoolValue) bval).val) {
                        return null;
                    }
                } else {
                    final UniqueString varName = var.getName();
                    final Value lval = (Value) s1.lookup(varName);
                    final Value rval = this.eval(args[1], c, s0, s1, EvalControl.Enabled, cm);
                    if (lval == null) {
                        if (!(rval instanceof Enumerable)) {
                            Assert.fail("The right side of \\IN is not enumerable.\n" + pred, pred, c);
                        }
                        final ValueEnumeration Enum = ((Enumerable) rval).elements();
                        Value val;
                        while ((val = Enum.nextElement()) != null) {
                            TLCState s2 = s1.bind(var, val);
                            s2 = this.enabled(acts, s0, s2, cm);
                            if (s2 != null) {
                                return s2;
                            }
                        }
                        return null;
                    } else {
                        if (!rval.member(lval)) {
                            return null;
                        }
                    }
                }
                return this.enabled(acts, s0, s1, cm);
            }

            // The following case added by LL on 13 Nov 2009 to handle subexpression names.
            case OPCODE_nop -> {
                return this.enabled(args[0], acts, c, s0, s1, cm);
            }
            default -> {
                // We handle all the other builtin operators here.
                final Value bval = this.eval(pred, c, s0, s1, EvalControl.Enabled, cm);
                if (!(bval instanceof BoolValue)) {
                    Assert.fail(EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING, new String[]{"ENABLED", "boolean",
                            bval.toString(), pred.toString()}, pred, c);
                }
                if (((BoolValue) bval).val) {
                    return this.enabled(acts, s0, s1, cm);
                }
                return null;
            }
        }
    }

    protected abstract TLCState enabledUnchanged(SemanticNode expr, ActionItemList acts,
                                                 Context c, TLCState s0, TLCState s1, CostModel cm);

    protected final TLCState enabledUnchangedImpl(final SemanticNode expr, final ActionItemList acts,
                                                  final Context c, final TLCState s0, TLCState s1, CostModel cm) {
        if (coverage) {
            cm = cm.get(expr);
        }
        final SymbolNode var = this.getVar(expr, c, true, toolId);
        if (var != null) {
            // a state variable, e.g. UNCHANGED var1
            final UniqueString varName = var.getName();
            final Value v0 = this.eval(expr, c, s0, s1, EvalControl.Enabled, cm);
            final IValue v1 = s1.lookup(varName);
            if (v1 == null) {
                s1 = s1.bind(var, v0);
                return this.enabled(acts, s0, s1, cm);
            }
            if (v1.equals(v0)) {
                return this.enabled(acts, s0, s1, cm);
            }
            MP.printWarning(EC.TLC_UNCHANGED_VARIABLE_CHANGED, varName.toString(), expr.toString());
            return null;
        }

        if (expr instanceof final OpApplNode expr1) {
            final ExprOrOpArgNode[] args = expr1.getArgs();
            final int alen = args.length;
            final SymbolNode opNode = expr1.getOperator();
            final UniqueString opName = opNode.getName();
            final int opcode = BuiltInOPs.getOpCode(opName);

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
                final Object val = this.lookup(opNode, c, false);

                if (val instanceof final LazyValue lv) {
                    return this.enabledUnchanged(lv.expr, acts, lv.con, s0, s1, cm);
                } else if (val instanceof OpDefNode odn) {
                    return this.enabledUnchanged(odn.getBody(), acts, c, s0, s1, cm);
                } else if (val == null) {
                    Assert.fail("In computing ENABLED, TLC found the undefined identifier\n" +
                            opName + " in an UNCHANGED expression at\n" + expr, expr, c);
                }
                return this.enabled(acts, s0, s1, cm);
            }
        }

        final Value v0 = this.eval(expr, c, s0, EmptyState, EvalControl.Enabled, cm);
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
        final Value v1 = this.eval(expr, c, s1, EmptyState, EvalControl.Primed, cm);
        if (!v0.equals(v1)) {
            return null;
        }
        return this.enabled(acts, s0, s1, cm);
    }

    /* This method determines if the action predicate is valid in (s0, s1). */
    @Override
    public final boolean isValid(final Action act, final TLCState s0, final TLCState s1) {
        final Value val = this.eval(act.pred, act.con, s0, s1, EvalControl.Clear, act.cm);
        if (!(val instanceof BoolValue)) {
            Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", act.pred.toString()}, act.pred, act.con);
        }
        return ((BoolValue) val).val;
    }

    /* Returns true iff the predicate is valid in the state. */
    @Override
    public boolean isValid(final Action act, final TLCState state) {
        return this.isValid(act, state, EmptyState);
    }

    /* Returns true iff the predicate is valid in the state. */
    @Override
    public final boolean isValid(final Action act) {
        return this.isValid(act, EmptyState, EmptyState);
    }

    @Override
    public boolean isValid(final ExprNode expr, final Context ctxt) {
        final IValue val = this.eval(expr, ctxt, EmptyState, EmptyState,
                EvalControl.Const, CostModel.DO_NOT_RECORD);
        if (!(val instanceof BoolValue)) {
            Assert.fail(EC.TLC_EXPECTED_VALUE, new String[]{"boolean", expr.toString()}, expr);
        }
        return ((BoolValue) val).val;
    }

    @Override
    public final boolean isValid(final ExprNode expr) {
        return isValid(expr, Context.Empty);
    }

    public boolean isValidAssumption(final ExprNode assumption) {
        return isValid(assumption);
    }

    @Override
    public final int checkAssumptions() {
        final ExprNode[] assumps = getAssumptions();
        final boolean[] isAxiom = getAssumptionIsAxiom();
        for (int i = 0; i < assumps.length; i++) {
            try {
                if ((!isAxiom[i]) && !isValidAssumption(assumps[i])) {
                    return MP.printError(EC.TLC_ASSUMPTION_FALSE, assumps[i].toString());
                }
            } catch (final Exception e) {
                // Assert.printStack(e);
                return MP.printError(EC.TLC_ASSUMPTION_EVALUATION_ERROR,
                        new String[]{assumps[i].toString(), e.getMessage()});
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

    private int checkPostConditionWithContext(final Context ctxt) {
        // User request: http://discuss.tlapl.us/msg03658.html
        final ExprNode[] postConditions = getPostConditionSpecs();
        for (final ExprNode en : postConditions) {
            try {
                if (!isValid(en, ctxt)) {
                    // It's not an assumption because the expression doesn't appear inside
                    // an ASSUME, but good enough for this prototype.
                    return MP.printError(EC.TLC_ASSUMPTION_FALSE, en.toString());
                }
            } catch (final Exception e) {
                // tool.isValid(sn) failed to evaluate...
                return MP.printError(EC.TLC_ASSUMPTION_EVALUATION_ERROR,
                        new String[]{en.toString(), e.getMessage()});
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

            public InitStateSelectorFunctor(final long fp) {
                this.fp = fp;
            }

            @Override
            public Object addState(final TLCState state) {
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
     * the stateNumber (relative to the given sinfo) and a pointer to
     * the predecessor.
     */
    @Override
    public final TLCStateInfo getState(final long fp, final TLCStateInfo sinfo) {
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
    public final TLCStateInfo getState(final long fp, final TLCState s) {
        IdThread.setCurrentState(s);
        for (final Action curAction : this.actions) {
            final StateVec nextStates = this.getNextStates(curAction, s);
            for (final TLCState state : nextStates) {
                final long nfp = state.fingerPrint();
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
    public final TLCStateInfo getState(final TLCState s1, final TLCState s) {
        IdThread.setCurrentState(s);
        for (final Action curAction : this.actions) {
            final StateVec nextStates = this.getNextStates(curAction, s);
            for (final TLCState state : nextStates) {
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
        if (name.length() == 0) {
            return null;
        }
        final Object symm = this.unprocessedDefns.get(name);
        if (symm == null) {
            Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[]{"symmetry function", name});
        }
        if (!(symm instanceof OpDefNode)) {
            Assert.fail("The symmetry function " + name + " must specify a set of permutations.");
        }
        final OpDefNode opDef = (OpDefNode) symm;
        // This calls tlc2.module.TLC.Permutations(Value) and returns a Value of |fcns|
        // = n! where n is the capacity of the symmetry set.
        final IValue fcns = this.eval(opDef.getBody(), Context.Empty, EmptyState, CostModel.DO_NOT_RECORD);
        if (!(fcns instanceof SetEnumValue)) {
            Assert.fail("The symmetry operator must specify a set of functions.", opDef.getBody());
        }
        final List<Value> values = ((SetEnumValue) fcns).elements().all();
        for (final Value v : values) {
            if (!(v instanceof FcnRcdValue)) {
                Assert.fail("The symmetry values must be function records.", opDef.getBody());
            }
        }
        final ExprOrOpArgNode[] argNodes = ((OpApplNode) opDef.getBody()).getArgs();
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
            subgroup = MVPerms.permutationSubgroup((Enumerable) fcns);
            final HashSet<ModelValue> subgroupMembers = new HashSet<>();
            for (final IMVPerm imvp : subgroup) {
                if (imvp instanceof MVPerm mvp) { // should always be the case
                    subgroupMembers.addAll(mvp.getAllModelValues());
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
                    plurality, cardinalityOneSetList.toString(), toHaveConjugation, antiPlurality);
        }

        return subgroup;
    }

    /**
     * Teases the original spec name for the set out of node and appends it to the {@code StringBuilder} instance.
     */
    private void addToSubTwoSizedSymmetrySetList(final ExprOrOpArgNode node, final StringBuilder cardinalityOneSetList) {
        final SyntaxTreeNode tn = (SyntaxTreeNode) node.getTreeNode();
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
     * @return if the node represents a permutation, this will return the {@link SetEnumValue} instance contains its
     * model values
     */
    private SetEnumValue getSetEnumValueFromArgumentNode(final ExprOrOpArgNode node) {
        if (node instanceof final OpApplNode permutationNode) {
            if (permutationNode.getOperator() instanceof final OpDefNode operator) {
                if (TLAConstants.BuiltInOperators.PERMUTATIONS.equals(operator.getName().toString())) {
                    final ExprOrOpArgNode[] operands = permutationNode.getArgs();
                    if ((operands.length == 1)
                            && (operands[0] instanceof OpApplNode oan)
                            && (oan.getOperator() instanceof OpDefOrDeclNode)) {
                        final Object o = oan.getOperator().getToolObject(toolId);

                        if (o instanceof SetEnumValue sev) {
                            return sev;
                        } else if (o instanceof final WorkerValue wv) {
                            // If TLC was started with a -workers N specification, N > 1, o will be a WorkerValue instance
                            final Object unwrapped = WorkerValue.mux(wv);

                            if (unwrapped instanceof SetEnumValue sev) {
                                return sev;
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
    public final Context getFcnContext(final IFcnLambdaValue fcn, final ExprOrOpArgNode[] args,
                                       final Context c, final TLCState s0, final TLCState s1,
                                       final int control) {
        return getFcnContext(fcn, args, c, s0, s1, control, CostModel.DO_NOT_RECORD);
    }

    @Override
    public final Context getFcnContext(final IFcnLambdaValue fcn, final ExprOrOpArgNode[] args,
                                       final Context c, final TLCState s0, final TLCState s1,
                                       final int control, final CostModel cm) {
        Context fcon = fcn.getCon();
        final int plen = fcn.getParams().length();
        final FormalParamNode[][] formals = fcn.getParams().getFormals();
        final Value[] domains = (Value[]) fcn.getParams().getDomains();
        final boolean[] isTuples = fcn.getParams().isTuples();
        final Value argVal = this.eval(args[1], c, s0, s1, control, cm);

        if (plen == 1) {
            if (!domains[0].member(argVal)) {
                Assert.fail("In applying the function\n" + Values.ppr(fcn.toString()) +
                        ",\nthe first argument is:\n" + Values.ppr(argVal.toString()) +
                        "which is not in its domain.\n" + args[0], args[0], c);
            }
            if (isTuples[0]) {
                final FormalParamNode[] ids = formals[0];
                final TupleValue tv = (TupleValue) argVal.toTuple();
                if (tv == null || argVal.size() != ids.length) {
                    Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                            ",\nthe argument is:\n" + Values.ppr(argVal.toString()) +
                            "which does not match its formal parameter.\n" + args[0], args[0], c);
                }
                final Value[] elems = Objects.requireNonNull(tv).elems;
                for (int i = 0; i < ids.length; i++) {
                    fcon = fcon.cons(ids[i], elems[i]);
                }
            } else {
                fcon = fcon.cons(formals[0][0], argVal);
            }
        } else {
            final TupleValue tv = (TupleValue) argVal.toTuple();
            if (tv == null) {
                Assert.fail("Attempted to apply a function to an argument not in its" +
                        " domain.\n" + args[0], args[0], c);
            }
            int argn = 0;
            final Value[] elems = Objects.requireNonNull(tv).elems;
            for (int i = 0; i < formals.length; i++) {
                final FormalParamNode[] ids = formals[i];
                final Value domain = domains[i];
                if (isTuples[i]) {
                    if (!domain.member(elems[argn])) {
                        Assert.fail("In applying the function\n" + Values.ppr(fcn.toString()) +
                                ",\nthe argument number " + (argn + 1) + " is:\n" +
                                Values.ppr(elems[argn].toString()) +
                                "\nwhich is not in its domain.\n" + args[0], args[0], c);
                    }
                    final TupleValue tv1 = (TupleValue) elems[argn++].toTuple();
                    if (tv1 == null || tv1.size() != ids.length) {
                        Assert.fail("In applying the function\n" + Values.ppr(fcn.toString()) +
                                ",\nthe argument number " + argn + " is:\n" +
                                Values.ppr(elems[argn - 1].toString()) +
                                "which does not match its formal parameter.\n" + args[0], args[0], c);
                    }
                    final Value[] avals = Objects.requireNonNull(tv1).elems;
                    for (int j = 0; j < ids.length; j++) {
                        fcon = fcon.cons(ids[j], avals[j]);
                    }
                } else {
                    for (final FormalParamNode id : ids) {
                        if (!domain.member(elems[argn])) {
                            Assert.fail("In applying the function\n" + Values.ppr(fcn.toString()) +
                                    ",\nthe argument number " + (argn + 1) + " is:\n" +
                                    Values.ppr(elems[argn].toString()) +
                                    "which is not in its domain.\n" + args[0], args[0], c);
                        }
                        fcon = fcon.cons(id, elems[argn++]);
                    }
                }
            }
        }
        return fcon;
    }

    @Override
    public final IContextEnumerator contexts(final OpApplNode appl, final Context c, final TLCState s0,
                                             final TLCState s1, final int control) {
        return contexts(appl, c, s0, s1, control, CostModel.DO_NOT_RECORD);
    }

    /* A context enumerator for an operator application. */
    public final IContextEnumerator contexts(final OpApplNode appl, final Context c, final TLCState s0,
                                             final TLCState s1, final int control, final CostModel cm) {
        return contexts(Ordering.NORMALIZED, appl, c, s0, s1, control, cm);
    }

    private IContextEnumerator contexts(final Ordering ordering, final OpApplNode appl, final Context c, final TLCState s0, final TLCState s1, final int control,
                                        final CostModel cm) {
        final FormalParamNode[][] formals = appl.getBdedQuantSymbolLists();
        final boolean[] isTuples = appl.isBdedQuantATuple();
        final ExprNode[] domains = appl.getBdedQuantBounds();

        final int flen = formals.length;
        int alen = 0;
        for (int i = 0; i < flen; i++) {
            alen += (isTuples[i]) ? 1 : formals[i].length;
        }
        final Object[] vars = new Object[alen];
        final ValueEnumeration[] enums = new ValueEnumeration[alen];
        int idx = 0;
        for (int i = 0; i < flen; i++) {
            final Value boundSet = this.eval(domains[i], c, s0, s1, control, cm);
            if (!(boundSet instanceof Enumerable)) {
                Assert.fail("TLC encountered a non-enumerable quantifier bound\n" +
                        Values.ppr(boundSet.toString()) + ".\n" + domains[i], domains[i], c);
            }
            final FormalParamNode[] farg = formals[i];
            if (isTuples[i]) {
                vars[idx] = farg;
                enums[idx++] = ((Enumerable) boundSet).elements(ordering);
            } else {
                for (final FormalParamNode formalParamNode : farg) {
                    vars[idx] = formalParamNode;
                    enums[idx++] = ((Enumerable) boundSet).elements(ordering);
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
    public Context getOpContext(final OpDefNode odn, final ExprOrOpArgNode[] args, final Context ctx, final boolean b) {
        return getOpContext(odn, args, ctx, b, toolId);
    }

    @Override
    public Object lookup(final SymbolNode opNode, final Context con, final boolean b) {
        return lookup(opNode, con, b, toolId);
    }

    @Override
    public Object getVal(final ExprOrOpArgNode expr, final Context con, final boolean b) {
        return getVal(expr, con, b, toolId);
    }

    /**
     * Users will likely want to call only {@link #getLevelBound(SemanticNode, Context, int)} - this
     * method is called from that method in certain cases.
     */
    public int getLevelBoundAppl(final OpApplNode expr, Context c, final int forToolId) {
        final SymbolNode opNode = expr.getOperator();
        final UniqueString opName = opNode.getName();
        final int opcode = BuiltInOPs.getOpCode(opName);

        if (BuiltInOPs.isTemporal(opcode)) {
            return 3; // Conservative estimate
        }

        if (BuiltInOPs.isAction(opcode)) {
            return 2; // Conservative estimate
        }

        if (opcode == ToolGlobals.OPCODE_enabled) {
            return 1; // Conservative estimate
        }

        int level = 0;
        final ExprNode[] bnds = expr.getBdedQuantBounds();
        for (final ExprNode bnd : bnds) {
            level = Math.max(level, getLevelBound(bnd, c, forToolId));
        }

        if (opcode == ToolGlobals.OPCODE_rfs) {
            // For recursive function, don't compute level of the function body
            // again in the recursive call.
            final SymbolNode fname = expr.getUnbdedQuantSymbols()[0];
            c = c.cons(fname, IntValue.ValOne);
        }

        final ExprOrOpArgNode[] args = expr.getArgs();
        for (final ExprOrOpArgNode arg : args) {
            if (arg != null) {
                level = Math.max(level, getLevelBound(arg, c, forToolId));
            }
        }

        if (opcode == 0) {
            // This operator is a user-defined operator.
            if (opName.getVarLoc(variables.length) >= 0)
                return 1;

            final Object val = lookup(opNode, c, false, forToolId);
            if (val instanceof final OpDefNode opDef) {
                c = c.cons(opNode, IntValue.ValOne);
                level = Math.max(level, getLevelBound(opDef.getBody(), c, forToolId));
            } else if (val instanceof final LazyValue lv) {
                level = Math.max(level, getLevelBound(lv.expr, lv.con, forToolId));
            } else if (val instanceof final EvaluatingValue ev) {
                level = Math.max(level, ev.getMinLevel());
            } else if (val instanceof final MethodValue mv) {
                level = Math.max(level, mv.getMinLevel());
            }
        }
        return level;
    }

    public enum Mode {
        Simulation, MC, MC_DEBUG, Executor
    }
}
