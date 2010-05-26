// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 19 May 2008 at  1:13:48 PST by lamport
//      modified on Fri Aug 24 14:43:24 PDT 2001 by yuanyu

package tlc2.tool;

import java.io.Serializable;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;

import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.DecimalNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LabelNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.APSubstInNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.TheoremNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.util.Context;
import tlc2.util.List;
import tlc2.util.ObjLongTable;
import tlc2.util.Vect;
import tlc2.value.BoolValue;
import tlc2.value.IntValue;
import tlc2.value.LazyValue;
import tlc2.value.MethodValue;
import tlc2.value.ModelValue;
import tlc2.value.OpRcdValue;
import tlc2.value.SetEnumValue;
import tlc2.value.StringValue;
import tlc2.value.Value;
import tlc2.value.ValueConstants;
import util.Assert;
import util.FilenameToStream;
import util.ToolIO;
import util.UniqueString;

public class Spec implements ValueConstants, ToolGlobals, Serializable
{

    public String specDir; // The spec directory.
    public String rootFile; // The root file of this spec.
    protected String configFile; // The model config file.
    protected ModelConfig config; // The model configuration.
    protected ExternalModuleTable moduleTbl; // The external modules reachable from root
    protected ModuleNode rootModule; // The root module.
    protected Defns defns; // Global definitions reachable from root
    // SZ 10.04.2009: changed the name of the variable to reflect its nature
    public OpDeclNode[] variablesNodes; // The state variables.
    protected TLAClass tlaClass; // TLA built-in classes.
    protected Vect initPredVec; // The initial state predicate.
    protected Action nextPred; // The next state predicate.
    protected Action[] temporals; // Fairness specifications...
    protected String[] temporalNames; // ... and their names
    protected Action[] impliedTemporals; // Liveness conds to check...
    protected String[] impliedTemporalNames; // ... and their names
    protected Action[] invariants; // Invariants to be checked...
    protected String[] invNames; // ... and their names
    protected Action[] impliedInits; // Implied-inits to be checked...
    protected String[] impliedInitNames; // ... and their names
    protected Action[] impliedActions; // Implied-actions to be checked...
    protected String[] impliedActNames; // ... and their names
    protected ExprNode[] modelConstraints; // Model constraints
    protected ExprNode[] actionConstraints; // Action constraints
    protected ExprNode[] assumptions; // Assumptions
    protected boolean[] assumptionIsAxiom; // assumptionIsAxiom[i] is true iff assumptions[i]
                                           // is an AXIOM.  Added 26 May 2010 by LL
    private FilenameToStream resolver; // takes car of path to stream resoltion

    public Spec(String specDir, String file, FilenameToStream resolver)
    {

        this.specDir = specDir;
        this.rootFile = file;
        this.rootModule = null;
        this.config = null;
        this.moduleTbl = null;
        this.variablesNodes = null;
        this.defns = new Defns();
        this.tlaClass = new TLAClass("tlc2.module");
        this.initPredVec = new Vect(5);
        this.nextPred = null;
        this.temporals = null;
        this.temporalNames = null;
        this.impliedTemporals = null;
        this.impliedTemporalNames = null;
        this.invariants = null;
        this.invNames = null;
        this.impliedInits = null;
        this.impliedInitNames = null;
        this.impliedActions = null;
        this.impliedActNames = null;
        this.modelConstraints = null;
        this.actionConstraints = null;
        this.assumptions = null;
        this.assumptionIsAxiom = null;  // added 26 May 2010 by LL
        this.resolver = resolver;
    }

    // SZ Feb 20, 2009: added support to name resolver, to be able to run outside of the tool
    public Spec(String specDir, String specFile, String configFile, FilenameToStream resolver)
    {
        this(specDir, specFile, resolver);
        // SZ Mar 9, 2009: added initialization of the modelValue class
        ModelValue.init();
        this.configFile = configFile;
        this.config = new ModelConfig(configFile + ".cfg", resolver);
        this.config.parse();
        ModelValue.setValues(); // called after seeing all model values
    }

    /**
     * Processes the specification and collects information to be used
     * by tools. The processing tries to use any customized module (Java
     * class) to override the corresponding TLA+ module.
     */
    // SZ Feb 20, 2009: added support for existing specObj
    protected final void processSpec(SpecObj spec)
    {

        if (spec == null)
        {
            // construct new specification object, if the
            // passed one was null
            spec = new SpecObj(this.rootFile, resolver);

            // We first call the SANY front-end to parse and semantic-analyze
            // the complete TLA+ spec starting with the main module rootFile.
            if (TLCGlobals.tool)
            {
                MP.printMessage(EC.TLC_SANY_START);
            }
            try
            {
                // SZ Feb 20, 2009:
                // call SANY to parse the module
                // this method will not throw any exceptions on
                // checked errors (init, parse, semantic).
                // Only if something unexpected happens the
                // exception is thrown
                SANY.frontEndMain(spec, this.rootFile, ToolIO.out);
            } catch (FrontEndException e)
            {
                Assert.fail(EC.TLC_PARSING_FAILED2, e);
            }

            if (TLCGlobals.tool)
            {
                MP.printMessage(EC.TLC_SANY_END);
            }

        }

        // SZ Feb 20, 2009:
        // since failed parsing is not marked by an exception,
        // check the status of the spec
        // check if the specification has been successfully created
        if (!spec.initErrors.isSuccess() || !spec.parseErrors.isSuccess() || !spec.semanticErrors.isSuccess())
        {
            Assert.fail(EC.TLC_PARSING_FAILED);
        }

        // Set the rootModule:
        this.moduleTbl = spec.getExternalModuleTable();
        UniqueString rootName = UniqueString.uniqueStringOf(this.rootFile);
        this.rootModule = this.moduleTbl.getModuleNode(rootName);

        // Get all the state variables in the spec:
        OpDeclNode[] varDecls = this.rootModule.getVariableDecls();

        this.variablesNodes = new OpDeclNode[varDecls.length];
        UniqueString[] varNames = new UniqueString[varDecls.length];

        for (int i = 0; i < varDecls.length; i++)
        {
            this.variablesNodes[i] = varDecls[i];
            varNames[i] = varDecls[i].getName();
            varNames[i].setLoc(i);
        }

        // set variables to the static filed in the state
        TLCState.setVariables(this.variablesNodes);

        // SZ 11.04.2009: set the number of variables
        UniqueString.setVariableCount(varDecls.length);

        // SZ 10.04.2009: moved the initialization
        // removed static initialization
        // Defns.init();
        // this seems strange, since the size of the definition table has been set during
        // creation of the Defn object. The reset of the number of definition does not affect the size
        // of the table
        this.defns.setDefnCount(varDecls.length);

        // Add predefined (Boolean and String) in defns.
        this.defns.put("TRUE", ValTrue);
        this.defns.put("FALSE", ValFalse);
        Value[] elems = new Value[2];
        elems[0] = ValFalse;
        elems[1] = ValTrue;
        this.defns.put("BOOLEAN", new SetEnumValue(elems, true));

        Class stringModule = this.tlaClass.loadClass("Strings");
        if (stringModule == null)
        {

            Assert.fail(EC.TLC_STRING_MODULE_NOT_FOUND);
        }
        Method[] ms = stringModule.getDeclaredMethods();
        for (int i = 0; i < ms.length; i++)
        {
            int mod = ms[i].getModifiers();
            if (Modifier.isStatic(mod))
            {
                String name = TLARegistry.mapName(ms[i].getName());
                int acnt = ms[i].getParameterTypes().length;
                MethodValue mv = new MethodValue(ms[i]);
                Value val = (acnt == 0) ? mv.apply(EmptyArgs, EvalControl.Clear) : mv;
                this.defns.put(name, val);
            }
        }

        // Process all the constants in the spec. Note that this must be done
        // here since we use defns. Things added into defns later will make it
        // wrong to use it in the method processConstants.
        ModuleNode[] mods = this.moduleTbl.getModuleNodes();
        HashSet modSet = new HashSet();
        for (int i = 0; i < mods.length; i++)
        {
            this.processConstants(mods[i]);
            modSet.add(mods[i].getName().toString());
        }

        // Collect all the assumptions.
        AssumeNode[] assumes = this.rootModule.getAssumptions();
        this.assumptions = new ExprNode[assumes.length];
        this.assumptionIsAxiom = new boolean[assumes.length];
        for (int i = 0; i < assumes.length; i++)
        {
            this.assumptions[i] = assumes[i].getAssume();
            this.assumptionIsAxiom[i] = assumes[i].getIsAxiom();
        }

        // Get the constants and overrides in config file.
        // Note: Both hash tables use String as key.
        Hashtable constants = this.initializeConstants();
        Hashtable overrides = this.config.getOverrides();

        // Apply config file constants to the constant decls visible to rootModule.
        OpDeclNode[] rootConsts = this.rootModule.getConstantDecls();
        for (int i = 0; i < rootConsts.length; i++)
        {
            UniqueString name = rootConsts[i].getName();
            Object val = constants.get(name.toString());
            if (val == null && !overrides.containsKey(name.toString()))
            {
                Assert.fail(EC.TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM, name.toString());
            }
            rootConsts[i].setToolObject(TLCGlobals.ToolId, val);
            this.defns.put(name, val);
        }

        // Apply config file constants to the operator defns visible to rootModule.
        OpDefNode[] rootOpDefs = this.rootModule.getOpDefs();
        for (int i = 0; i < rootOpDefs.length; i++)
        {
            UniqueString name = rootOpDefs[i].getName();
            Object val = constants.get(name.toString());
            if (val == null)
            {
                this.defns.put(name, rootOpDefs[i]);
            } else
            {
                rootOpDefs[i].setToolObject(TLCGlobals.ToolId, val);
                this.defns.put(name, val);
            }
        }

        // Apply config file module specific constants to operator defns.
        // We do not allow this kind of replacement for constant decls.
        Hashtable modConstants = this.initializeModConstants();
        for (int i = 0; i < mods.length; i++)
        {
            UniqueString modName = mods[i].getName();
            Hashtable mConsts = (Hashtable) modConstants.get(modName.toString());
            if (mConsts != null)
            {
                OpDefNode[] opDefs = mods[i].getOpDefs();
                for (int j = 0; j < opDefs.length; j++)
                {
                    UniqueString name = opDefs[j].getName();
                    Object val = mConsts.get(name.toString());
                    if (val != null)
                    {
                        opDefs[j].getBody().setToolObject(TLCGlobals.ToolId, val);
                    }
                }
            }
        }

        // Apply module overrides:
        for (int i = 0; i < mods.length; i++)
        {
            UniqueString modName = mods[i].getName();
            Class userModule = this.tlaClass.loadClass(modName.toString());
            if (userModule != null)
            {
                // Override with a user defined Java class for the TLA+ module.
                // Collects new definitions:
                Hashtable javaDefs = new Hashtable();
                Method[] mds = userModule.getDeclaredMethods();
                for (int j = 0; j < mds.length; j++)
                {
                    int mdf = mds[j].getModifiers();
                    if (Modifier.isPublic(mdf) && Modifier.isStatic(mdf))
                    {
                        String name = TLARegistry.mapName(mds[j].getName());
                        UniqueString uname = UniqueString.uniqueStringOf(name);
                        int acnt = mds[j].getParameterTypes().length;
                        MethodValue mv = new MethodValue(mds[j]);
                        boolean isConstant = (acnt == 0) && Modifier.isFinal(mdf);
                        Value val = isConstant ? mv.apply(EmptyArgs, EvalControl.Clear) : mv;
                        javaDefs.put(uname, val);
                    }
                }
                // Adds/overrides new definitions:
                OpDefNode[] opDefs = mods[i].getOpDefs();
                for (int j = 0; j < opDefs.length; j++)
                {
                    UniqueString uname = opDefs[j].getName();
                    Object val = javaDefs.get(uname);
                    if (val != null)
                    {
                        opDefs[j].getBody().setToolObject(TLCGlobals.ToolId, val);
                        this.defns.put(uname, val);
                    }
                }
            }
        }

        HashSet overriden = new HashSet();
        // Apply config file overrides to constants:
        for (int i = 0; i < rootConsts.length; i++)
        {
            UniqueString lhs = rootConsts[i].getName();
            String rhs = (String) overrides.get(lhs.toString());
            if (rhs != null)
            {
                if (overrides.containsKey(rhs))
                {
                    Assert.fail(EC.TLC_CONFIG_RHS_ID_APPEARED_AFTER_LHS_ID, rhs);
                }
                Object myVal = this.defns.get(rhs);
                if (myVal == null)
                {
                    Assert.fail(EC.TLC_CONFIG_WRONG_SUBSTITUTION, new String[] { lhs.toString(), rhs });
                }
                rootConsts[i].setToolObject(TLCGlobals.ToolId, myVal);
                this.defns.put(lhs, myVal);
                overriden.add(lhs.toString());
            }
        }

        // Apply config file overrides to operator definitions:
        for (int i = 0; i < rootOpDefs.length; i++)
        {
            UniqueString lhs = rootOpDefs[i].getName();
            String rhs = (String) overrides.get(lhs.toString());
            if (rhs != null)
            {
                if (overrides.containsKey(rhs))
                {
                    Assert.fail(EC.TLC_CONFIG_RHS_ID_APPEARED_AFTER_LHS_ID, rhs);
                }
                Object myVal = this.defns.get(rhs);
                if (myVal == null)
                {
                    Assert.fail(EC.TLC_CONFIG_WRONG_SUBSTITUTION, new String[] { lhs.toString(), rhs });
                }
                if ((myVal instanceof OpDefNode)
                        && rootOpDefs[i].getNumberOfArgs() != ((OpDefNode) myVal).getNumberOfArgs())
                {
                    Assert.fail(EC.TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS, new String[] { lhs.toString(), rhs });
                }
                rootOpDefs[i].setToolObject(TLCGlobals.ToolId, myVal);
                this.defns.put(lhs, myVal);
                overriden.add(lhs.toString());
            }
        }

        Enumeration keys = overrides.keys();
        while (keys.hasMoreElements())
        {
            Object key = keys.nextElement();
            if (!overriden.contains(key))
            {
                Assert.fail(EC.TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC, key.toString());
            }
        }

        // Apply config file module specific overrides to operator defns.
        // We do not allow this kind of replacement for constant decls.
        Hashtable modOverrides = this.config.getModOverrides();
        for (int i = 0; i < mods.length; i++)
        {
            UniqueString modName = mods[i].getName();
            Hashtable mDefs = (Hashtable) modOverrides.get(modName.toString());
            HashSet modOverriden = new HashSet();
            if (mDefs != null)
            {
                // the operator definitions:
                OpDefNode[] opDefs = mods[i].getOpDefs();
                for (int j = 0; j < opDefs.length; j++)
                {
                    UniqueString lhs = opDefs[j].getName();
                    String rhs = (String) mDefs.get(lhs.toString());
                    if (rhs != null)
                    {
                        if (mDefs.containsKey(rhs))
                        {
                            Assert.fail(EC.TLC_CONFIG_RHS_ID_APPEARED_AFTER_LHS_ID, rhs);
                        }
                        // The rhs comes from the root module.
                        Object myVal = this.defns.get(rhs);
                        if (myVal == null)
                        {
                            Assert.fail(EC.TLC_CONFIG_WRONG_SUBSTITUTION, new String[] { lhs.toString(), rhs });
                        }
                        if ((myVal instanceof OpDefNode)
                                && opDefs[j].getNumberOfArgs() != ((OpDefNode) myVal).getNumberOfArgs())
                        {
                            Assert.fail(EC.TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS, new String[] { lhs.toString(),
                                    rhs });
                        }
                        opDefs[j].getBody().setToolObject(TLCGlobals.ToolId, myVal);
                        modOverriden.add(lhs.toString());
                    }
                }

                Enumeration mkeys = mDefs.keys();
                while (mkeys.hasMoreElements())
                {
                    Object mkey = mkeys.nextElement();
                    if (!modOverriden.contains(mkey))
                    {
                        Assert.fail(EC.TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC, mkey.toString());
                    }
                }
            }
        }

        // Check if the module names specified in the config file are defined.
        Enumeration modKeys = modOverrides.keys();
        while (modKeys.hasMoreElements())
        {
            Object modName = modKeys.nextElement();
            if (!modSet.contains(modName))
            {
                Assert.fail(EC.TLC_NO_MODULES, modName.toString());
            }
        }
    }

    /*************************************************************************
     * The following method goes through all the nodes to set their           *
     * tool-specific fields.  It was modified on 1 May 2007 so it would find  *
     * the nodes in the body of a Lambda expression.  Obviously, if new       *
     * semantic node types are added, this method will have to be modified.   *
     * Less obviously, if a tool wants to call TLC on a specification that    *
     * was not all created inside a module, then this method may need to be   *
     * modified so TLC finds thos nodes not part of the module.               *
     *                                                                        *
     * Yuan claims that this is the only method in TLC that has to find all   *
     * the nodes in such a way.                                               *
     *************************************************************************/
    private final void processConstants(SemanticNode expr)
    {
        switch (expr.getKind()) {
        case ModuleKind: {
            ModuleNode expr1 = (ModuleNode) expr;
            // Process operator definitions:
            OpDefNode[] opDefs = expr1.getOpDefs();
            for (int i = 0; i < opDefs.length; i++)
            {
                Object def = opDefs[i].getToolObject(TLCGlobals.ToolId);
                if (def instanceof OpDefNode)
                {
                    this.processConstants(((OpDefNode) def).getBody());
                }
                this.processConstants(opDefs[i].getBody());
            }
            // Process all the inner modules:
            ModuleNode[] imods = expr1.getInnerModules();
            for (int i = 0; i < imods.length; i++)
            {
                this.processConstants(imods[i]);
            }
            // Process all the assumptions:
            AssumeNode[] assumps = expr1.getAssumptions();
            for (int i = 0; i < assumps.length; i++)
            {
                this.processConstants(assumps[i]);
            }
            // On 13 Nov 2009, Yuan Yu added the following
            // processing of all TheoremNodes, which was needed to
            // allow Theorem and Assumption names to be used as expressions.
            //
            // Process all the theorems:
            TheoremNode[] thms = expr1.getTheorems();
            for (int i = 0; i < thms.length; i++) {
              this.processConstants(thms[i]);
            }

            return;
        }
        case OpApplKind: {
            OpApplNode expr1 = (OpApplNode) expr;
            SymbolNode opNode = expr1.getOperator();
            Object val = this.defns.get(opNode.getName());
            if (val != null)
            {
                opNode.setToolObject(TLCGlobals.ToolId, val);
            } else
            {
                SemanticNode[] args = expr1.getArgs();
                for (int i = 0; i < args.length; i++)
                {
                    if (args[i] != null)
                    {
                        this.processConstants(args[i]);
                    }
                }
                ExprNode[] bnds = expr1.getBdedQuantBounds();
                for (int i = 0; i < bnds.length; i++)
                {
                    this.processConstants(bnds[i]);
                }
            }
            return;
        }
        case LetInKind: {
            LetInNode expr1 = (LetInNode) expr;
            OpDefNode[] letDefs = expr1.getLets();
            for (int i = 0; i < letDefs.length; i++)
            {
                this.processConstants(letDefs[i].getBody());
            }
            this.processConstants(expr1.getBody());
            return;
        }
        case SubstInKind: {
            SubstInNode expr1 = (SubstInNode) expr;
            Subst[] subs = expr1.getSubsts();
            for (int i = 0; i < subs.length; i++)
            {
                this.processConstants(subs[i].getExpr());
            }
            this.processConstants(expr1.getBody());
            return;
        }

        // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
        case APSubstInKind: {
            APSubstInNode expr1 = (APSubstInNode) expr;
            Subst[] subs = expr1.getSubsts();
            for (int i = 0; i < subs.length; i++)
            {
                this.processConstants(subs[i].getExpr());
            }
            this.processConstants(expr1.getBody());
            return;
        }


        case NumeralKind: {
            NumeralNode expr1 = (NumeralNode) expr;
            IntValue val = IntValue.gen(expr1.val());
            expr1.setToolObject(TLCGlobals.ToolId, val);
            return;
        }
        case DecimalKind: {
            DecimalNode expr1 = (DecimalNode) expr; // SZ: using typed variable
            Assert.fail(EC.TLC_CANT_HANDLE_REAL_NUMBERS, expr1.toString());
            return;
        }
        case StringKind: {
            StringNode expr1 = (StringNode) expr;
            StringValue val = new StringValue(expr1.getRep());
            expr1.setToolObject(TLCGlobals.ToolId, val);
            return;
        }
        case AssumeKind: {
            AssumeNode expr1 = (AssumeNode) expr;
            this.processConstants(expr1.getAssume());
            return;
        }
        // On 13 Nov 2009, Yuan Yu added the following case, which was
        // needed to allow Theorem and Assumption names to be used as 
        // expressions.
        //
        case TheoremKind:
          {
        TheoremNode expr1 = (TheoremNode)expr;
        this.processConstants(expr1.getTheorem());
        return;
          }
        case OpArgKind: {
            SymbolNode opArgNode = ((OpArgNode) expr).getOp();
            if (opArgNode.getKind() == UserDefinedOpKind)
            {
                this.processConstants(((OpDefNode) opArgNode).getBody());
            }
            return;
        }
            /***********************************************************************
             * LabelKind case added by LL on 13 Jun 2007.                           *
             ***********************************************************************/
        case LabelKind: {
            LabelNode expr1 = (LabelNode) expr;
            this.processConstants(expr1.getBody());
        }
        }
    }

    /* Return the variable if expr is a state variable. Otherwise, null. */
    public final SymbolNode getVar(SemanticNode expr, Context c, boolean cutoff)
    {
        if (expr instanceof OpApplNode)
        {
            SymbolNode opNode = ((OpApplNode) expr).getOperator();

            if (opNode.getArity() == 0)
            {
                boolean isVarDecl = (opNode.getKind() == VariableDeclKind);
                Object val = this.lookup(opNode, c, cutoff && isVarDecl);

                if (val instanceof LazyValue)
                {
                    LazyValue lval = (LazyValue) val;
                    return this.getVar(lval.expr, lval.con, cutoff);
                }
                if (val instanceof OpDefNode)
                {
                    return this.getVar(((OpDefNode) val).getBody(), c, cutoff);
                }
                if (isVarDecl)
                {
                    return opNode;
                }
            }
        }
        return null;
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
                return this.getVar(expr1.getArgs()[0], c, cutoff);
            }

            if (opNode.getArity() == 0)
            {
                boolean isVarDecl = (opNode.getKind() == VariableDeclKind);
                Object val = this.lookup(opNode, c, cutoff && isVarDecl);

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

    private Vect invVec = new Vect();
    private Vect invNameVec = new Vect();
    private Vect impliedInitVec = new Vect();
    private Vect impliedInitNameVec = new Vect();
    private Vect impliedActionVec = new Vect();
    private Vect impliedActNameVec = new Vect();
    private Vect temporalVec = new Vect();
    private Vect temporalNameVec = new Vect();
    private Vect impliedTemporalVec = new Vect();
    private Vect impliedTemporalNameVec = new Vect();

    /** 
     * Process the configuration file. 
     */
    public final void processConfig()
    {
        // Process the invariants:
        this.processConfigInvariants();

        // Process specification:
        String specName = this.config.getSpec();
        if (specName.length() == 0)
        {
            this.processConfigInitAndNext();
        } else
        {
            if (this.config.getInit().length() != 0 || this.config.getNext().length() != 0)
            {
                Assert.fail(EC.TLC_CONFIG_NOT_BOTH_SPEC_AND_INIT);
            }
            Object spec = this.defns.get(specName);
            if (spec instanceof OpDefNode)
            {
                OpDefNode opDef = (OpDefNode) spec;
                if (opDef.getArity() != 0)
                {
                    Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[] { specName });
                }
                this.processConfigSpec(opDef.getBody(), Context.Empty, List.Empty);
            } else if (spec == null)
            {
                Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "name", specName });
            } else
            {
                Assert.fail(EC.TLC_CONFIG_ID_HAS_VALUE, new String[] { "value", specName, spec.toString() });
            }
        }

        // Process the properties:
        Vect propNames = this.config.getProperties();
        for (int i = 0; i < propNames.size(); i++)
        {
            String propName = (String) propNames.elementAt(i);
            Object prop = this.defns.get(propName);
            if (prop instanceof OpDefNode)
            {
                OpDefNode opDef = (OpDefNode) prop;
                if (opDef.getArity() != 0)
                {
                    Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[] { propName });
                }
                this.processConfigProps(propName, opDef.getBody(), Context.Empty, List.Empty);
            } else if (prop == null)
            {
                Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "property", propName });
            } else if (!(prop instanceof BoolValue) || !(((BoolValue) prop).val))
            {
                Assert.fail(EC.TLC_CONFIG_ID_HAS_VALUE, new String[] { "property", propName, prop.toString() });
            }
        }

        // Postprocess:
        this.invariants = new Action[this.invVec.size()];
        this.invNames = new String[this.invVec.size()];
        for (int i = 0; i < this.invariants.length; i++)
        {
            this.invariants[i] = (Action) this.invVec.elementAt(i);
            this.invNames[i] = (String) this.invNameVec.elementAt(i);
        }
        this.invVec = null;
        this.invNameVec = null;

        this.impliedInits = new Action[this.impliedInitVec.size()];
        this.impliedInitNames = new String[this.impliedInitVec.size()];
        for (int i = 0; i < this.impliedInits.length; i++)
        {
            this.impliedInits[i] = (Action) this.impliedInitVec.elementAt(i);
            this.impliedInitNames[i] = (String) this.impliedInitNameVec.elementAt(i);
        }
        this.impliedInitVec = null;
        this.impliedInitNameVec = null;

        this.impliedActions = new Action[this.impliedActionVec.size()];
        this.impliedActNames = new String[this.impliedActionVec.size()];
        for (int i = 0; i < this.impliedActions.length; i++)
        {
            this.impliedActions[i] = (Action) this.impliedActionVec.elementAt(i);
            this.impliedActNames[i] = (String) this.impliedActNameVec.elementAt(i);
        }
        this.impliedActionVec = null;
        this.impliedActNameVec = null;

        this.temporals = new Action[this.temporalVec.size()];
        this.temporalNames = new String[this.temporalNameVec.size()];
        for (int i = 0; i < this.temporals.length; i++)
        {
            this.temporals[i] = (Action) this.temporalVec.elementAt(i);
            this.temporalNames[i] = (String) this.temporalNameVec.elementAt(i);
        }
        this.temporalVec = null;
        this.temporalNameVec = null;

        this.impliedTemporals = new Action[this.impliedTemporalVec.size()];
        this.impliedTemporalNames = new String[this.impliedTemporalNameVec.size()];
        for (int i = 0; i < this.impliedTemporals.length; i++)
        {
            this.impliedTemporals[i] = (Action) this.impliedTemporalVec.elementAt(i);
            this.impliedTemporalNames[i] = (String) this.impliedTemporalNameVec.elementAt(i);
        }
        this.impliedTemporalVec = null;
        this.impliedTemporalNameVec = null;

        if (this.initPredVec.size() == 0
                && (this.impliedInits.length != 0 || this.impliedActions.length != 0 || this.variablesNodes.length != 0
                        || this.invariants.length != 0 || this.impliedTemporals.length != 0))
        {
            Assert.fail(EC.TLC_CONFIG_MISSING_INIT);
        }
        if (this.nextPred == null
                && (this.impliedActions.length != 0 || this.invariants.length != 0 || this.impliedTemporals.length != 0))
        {
            Assert.fail(EC.TLC_CONFIG_MISSING_NEXT);
        }
    }

    /** 
     * Process the INIT and NEXT fields of the config file. 
     */
    private void processConfigInitAndNext()
    {
        String name = this.config.getInit();
        if (name.length() != 0)
        {
            Object init = this.defns.get(name);
            if (init == null)
            {
                Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "initial predicate", name });
            }
            if (!(init instanceof OpDefNode))
            {
                Assert.fail(EC.TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT, new String[] { "initial predicate", name });
            }
            OpDefNode def = (OpDefNode) init;
            if (def.getArity() != 0)
            {
                Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[] { "initial predicate", name });
            }
            this.initPredVec.addElement(new Action(def.getBody(), Context.Empty));
        }

        name = this.config.getNext();
        if (name.length() != 0)
        {
            Object next = this.defns.get(name);
            if (next == null)
            {
                Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "next state action", name });
            }
            if (!(next instanceof OpDefNode))
            {
                Assert.fail(EC.TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT, new String[] { "next state action", name });
            }
            OpDefNode def = (OpDefNode) next;
            if (def.getArity() != 0)
            {
                Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[] { "next state action", name });
            }
            this.nextPred = new Action(def.getBody(), Context.Empty);
        }
    }

    /** 
     * Process the INVARIANTS field of the config file. 
     */
    private void processConfigInvariants()
    {
        Vect invs = this.config.getInvariants();
        for (int i = 0; i < invs.size(); i++)
        {
            String name = (String) invs.elementAt(i);
            Object inv = this.defns.get(name);
            if (inv instanceof OpDefNode)
            {
                OpDefNode def = (OpDefNode) inv;
                if (def.getArity() != 0)
                {
                    Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[] { "invariant", name });
                }
                this.invNameVec.addElement(name);
                this.invVec.addElement(new Action(def.getBody(), Context.Empty));
            } else if (inv == null)
            {
                Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "invariant", name });
            } else if (!(inv instanceof BoolValue) || !(((BoolValue) inv).val))
            {
                Assert.fail(EC.TLC_CONFIG_ID_HAS_VALUE, new String[] { "invariant", name, inv.toString() });
            }
        }
    }

    /* Process the SPECIFICATION field of the config file.  */
    private final void processConfigSpec(ExprNode pred, Context c, List subs)
    {
        if (pred instanceof SubstInNode)
        {
            SubstInNode pred1 = (SubstInNode) pred;
            this.processConfigSpec(pred1.getBody(), c, subs.cons(pred1));
            return;
        }
        
        if (pred instanceof OpApplNode)
        {
            OpApplNode pred1 = (OpApplNode) pred;
            ExprOrOpArgNode[] args = pred1.getArgs();

            if (args.length == 0)
            {
                SymbolNode opNode = pred1.getOperator();
                Object val = this.lookup(opNode, c, false);
                if (val instanceof OpDefNode)
                {
                    if (((OpDefNode) val).getArity() != 0)
                    {
                        Assert.fail(EC.TLC_CONFIG_OP_NO_ARGS, new String[] { opNode.getName().toString() });
                    }
                    ExprNode body = ((OpDefNode) val).getBody();
                    if (this.getLevelBound(body, c) == 1)
                    {
                        this.initPredVec.addElement(new Action(Spec.addSubsts(body, subs), c));
                    } else
                    {
                        this.processConfigSpec(body, c, subs);
                    }
                } else if (val == null)
                {
                    Assert.fail(EC.TLC_CONFIG_OP_NOT_IN_SPEC, new String[] { opNode.getName().toString() });
                } else if (val instanceof BoolValue)
                {
                    if (!((BoolValue) val).val)
                    {
                        Assert.fail(EC.TLC_CONFIG_SPEC_IS_TRIVIAL, opNode.getName().toString());
                    }
                } else
                {
                    Assert
                            .fail(EC.TLC_CONFIG_OP_IS_EQUAL,
                                    new String[] { opNode.getName().toString(), val.toString(), "spec" });
                }
                return;
            }

            int opcode = BuiltInOPs.getOpCode(pred1.getOperator().getName());
            if (opcode == OPCODE_cl || opcode == OPCODE_land)
            {
                for (int i = 0; i < args.length; i++)
                {
                    this.processConfigSpec((ExprNode) args[i], c, subs);
                }
                return;
            }
            if (opcode == OPCODE_box)
            {
                SemanticNode boxArg = args[0];
                if ((boxArg instanceof OpApplNode)
                        && BuiltInOPs.getOpCode(((OpApplNode) boxArg).getOperator().getName()) == OPCODE_sa)
                {
                    ExprNode arg = (ExprNode) ((OpApplNode) boxArg).getArgs()[0];
                    // ---sm 09/06/04 <<<
                    ExprNode subscript = (ExprNode) ((OpApplNode) boxArg).getArgs()[1];
                    Vect varsInSubscript = null;
                    // collect the variables from the subscript...
                    try
                    {
                        class SubscriptCollector
                        {
                            /**
                             * This class attempts to recover all variables that
                             * appear in (possibly nested) tuples in the subscript
                             * of the next-state relation. Variables that appear
                             * in other kinds of expressions are ignored.
                             * The idea is to make sure that the subscript is a
                             * tuple that contains at least the declared variables
                             * of this specification object -- otherwise TLC's
                             * analysis is incorrect.
                             **/
                            Vect components;

                            SubscriptCollector()
                            {
                                this.components = new Vect();
                            }

                            void enter(ExprNode subscript, Context c)
                            {
                                // if it's a variable, add it to the vector and return
                                SymbolNode var = getVar(subscript, c, false);
                                if (var != null)
                                {
                                    components.addElement(var);
                                    return;
                                }
                                // otherwise further analyze the expression
                                switch (subscript.getKind()) {
                                case OpApplKind: {
                                    OpApplNode subscript1 = (OpApplNode) subscript;
                                    SymbolNode opNode = subscript1.getOperator();
                                    ExprOrOpArgNode[] args = subscript1.getArgs();
                                    int opCode = BuiltInOPs.getOpCode(opNode.getName());
                                    // if it's a tuple, recurse with its members
                                    if (opCode == OPCODE_tup)
                                    {
                                        for (int i = 0; i < args.length; i++)
                                        {
                                            this.enter((ExprNode) args[i], c);
                                        }
                                        return;
                                    }
                                    // all other built-in operators are ignored
                                    else if (opCode != 0)
                                    {
                                        return;
                                    }
                                    // user-defined operator: look up its definition
                                    Object opDef = lookup(opNode, c, false);
                                    if (opDef instanceof OpDefNode)
                                    {
                                        OpDefNode opDef1 = (OpDefNode) opDef;
                                        this.enter(opDef1.getBody(), getOpContext(opDef1, args, c, false));
                                        return;
                                    }
                                    if (opDef instanceof LazyValue)
                                    {
                                        LazyValue lv = (LazyValue) opDef;
                                        this.enter((ExprNode) lv.expr, lv.con);
                                        return;
                                    }
                                    // ignore overridden operators etc
                                    break;
                                }
                                case SubstInKind: {
                                    SubstInNode subscript1 = (SubstInNode) subscript;
                                    Subst[] subs = subscript1.getSubsts();
                                    Context c1 = c;
                                    for (int i = 0; i < subs.length; i++)
                                    {
                                        c1 = c1.cons(subs[i].getOp(), getVal(subs[i].getExpr(), c, false));
                                    }
                                    this.enter(subscript1.getBody(), c1);
                                    return;
                                }
                                case LetInKind: { // a bit strange, but legal...
                                    // note: the let-bound values become constants
                                    // so they are uninteresting for our purposes
                                    LetInNode subscript1 = (LetInNode) subscript;
                                    this.enter(subscript1.getBody(), c);
                                    return;
                                }
                                    /***********************************************************
                                    * LabelKind case added by LL on 13 Jun 2007.               *
                                    ***********************************************************/
                                case LabelKind: { // unlikely, but probably legal...
                                    LabelNode subscript1 = (LabelNode) subscript;
                                    this.enter((ExprNode) subscript1.getBody(), c);
                                    /*******************************************************
                                    * Cast to ExprNode added by LL on 19 May 2008 because  *
                                    * of change to LabelNode class.                        *
                                    *******************************************************/
                                    return;
                                }
                                default: // give up
                                    Assert.fail(EC.TLC_CANT_HANDLE_SUBSCRIPT, subscript.toString());
                                    return;
                                }
                            }

                            Vect getComponents()
                            {
                                return components;
                            }
                        }

                        SubscriptCollector collector = new SubscriptCollector();
                        Context c1 = c;
                        List subs1 = subs;
                        while (!subs1.isEmpty())
                        {
                            SubstInNode sn = (SubstInNode) subs1.car();
                            Subst[] snsubs = sn.getSubsts();
                            for (int i = 0; i < snsubs.length; i++)
                            {
                                c1 = c1.cons(snsubs[i].getOp(), getVal(snsubs[i].getExpr(), c, false));
                            }
                            subs1 = subs1.cdr();
                        }
                        collector.enter(subscript, c1);
                        varsInSubscript = collector.getComponents();
                    } catch (Exception e)
                    { // probably a ClassCastException
                        // Assert.printStack(e);
                        MP.printWarning(EC.TLC_COULD_NOT_DETERMINE_SUBSCRIPT, new String[0]);
                        varsInSubscript = null;
                    }
                    // ... and make sure they contain all the state variables
                    if (varsInSubscript != null)
                    {
                        for (int i = 0; i < this.variablesNodes.length; i++)
                        {
                            if (!varsInSubscript.contains(this.variablesNodes[i]))
                            {
                                // Assert.fail("The subscript of the next-state relation specified by the specification\ndoes not contain the state variable "
                                // + this.variables[i].getName());
                                MP.printWarning(EC.TLC_SUBSCRIPT_CONTAIN_NO_STATE_VAR,
                                        new String[] { this.variablesNodes[i].getName().toString() });
                            }
                        }
                    }
                    if (this.nextPred == null)
                    {
                        this.nextPred = new Action(Spec.addSubsts(arg, subs), c);
                    } else
                    {
                        Assert.fail(EC.TLC_CANT_HANDLE_TOO_MANY_NEXT_STATE_RELS);
                    }
                    // ---sm 09/06/04 >>>
                } else
                {
                    this.temporalVec.addElement(new Action(Spec.addSubsts(pred, subs), c));
                    this.temporalNameVec.addElement(pred.toString());
                }
                return;
            }
          // The following case added by LL on 13 Nov 2009 to handle subexpression names.
          if (opcode ==  OPCODE_nop)
           {
               this.processConfigSpec((ExprNode) args[0], c, subs);
               return;
           }
        }

        int level = this.getLevelBound(pred, c);
        if (level <= 1)
        {
            this.initPredVec.addElement(new Action(Spec.addSubsts(pred, subs), c));
        } else if (level == 3)
        {
            this.temporalVec.addElement(new Action(Spec.addSubsts(pred, subs), c));
            this.temporalNameVec.addElement(pred.toString());
        } else
        {
            Assert.fail(EC.TLC_CANT_HANDLE_CONJUNCT, pred.toString());
        }
    }

    /* Process the PROPERTIES field of the config file. */
    private final void processConfigProps(String name, ExprNode pred, Context c, List subs)
    {
        if (pred instanceof SubstInNode)
        {
            SubstInNode pred1 = (SubstInNode) pred;
            this.processConfigProps(name, pred1.getBody(), c, subs.cons(pred1));
            return;
        }
        if (pred instanceof OpApplNode)
        {
            OpApplNode pred1 = (OpApplNode) pred;
            ExprOrOpArgNode[] args = pred1.getArgs();
            if (args.length == 0)
            {
                SymbolNode opNode = pred1.getOperator();
                Object val = this.lookup(opNode, c, false);
                if (val instanceof OpDefNode)
                {
                    if (((OpDefNode) val).getArity() != 0)
                    {
                        Assert.fail(EC.TLC_CONFIG_OP_NO_ARGS, opNode.getName().toString());
                    }
                    this.processConfigProps(opNode.getName().toString(), ((OpDefNode) val).getBody(), c, subs);
                } else if (val == null)
                {
                    Assert.fail(EC.TLC_CONFIG_OP_NOT_IN_SPEC, opNode.getName().toString());
                } else if (val instanceof BoolValue)
                {
                    if (!((BoolValue) val).val)
                    {
                        Assert.fail(EC.TLC_CONFIG_SPEC_IS_TRIVIAL, opNode.getName().toString());
                    }
                } else
                {
                    Assert
                            .fail(EC.TLC_CONFIG_OP_IS_EQUAL,
                                    new String[] { opNode.getName().toString(), val.toString(), "property" });
                }
                return;
            }
            int opcode = BuiltInOPs.getOpCode(pred1.getOperator().getName());
            if (opcode == OPCODE_cl || opcode == OPCODE_land)
            {
                for (int i = 0; i < args.length; i++)
                {
                    ExprNode conj = (ExprNode) args[i];
                    this.processConfigProps(conj.toString(), conj, c, subs);
                }
                return;
            }
            if (opcode == OPCODE_box)
            {
                ExprNode boxArg = (ExprNode) args[0];
                if ((boxArg instanceof OpApplNode)
                        && BuiltInOPs.getOpCode(((OpApplNode) boxArg).getOperator().getName()) == OPCODE_sa)
                {
                    OpApplNode boxArg1 = (OpApplNode) boxArg;
                    if (boxArg1.getArgs().length == 0)
                    {
                        name = boxArg1.getOperator().getName().toString();
                    }
                    this.impliedActNameVec.addElement(name);
                    this.impliedActionVec.addElement(new Action(Spec.addSubsts(boxArg, subs), c));
                } else if (this.getLevelBound(boxArg, c) < 2)
                {
                    this.invVec.addElement(new Action(Spec.addSubsts(boxArg, subs), c));
                    if ((boxArg instanceof OpApplNode) && (((OpApplNode) boxArg).getArgs().length == 0))
                    {
                        name = ((OpApplNode) boxArg).getOperator().getName().toString();
                    }
                    this.invNameVec.addElement(name);
                } else
                {
                    this.impliedTemporalVec.addElement(new Action(Spec.addSubsts(pred, subs), c));
                    this.impliedTemporalNameVec.addElement(name);
                }
                return;
            }
          // The following case added by LL on 13 Nov 2009 to handle subexpression names.
          if (opcode ==  OPCODE_nop)
           {
               this.processConfigProps(name, (ExprNode) args[0], c, subs);
               return;
           }
        }
        int level = this.getLevelBound(pred, c);
        if (level <= 1)
        {
            this.impliedInitVec.addElement(new Action(Spec.addSubsts(pred, subs), c));
            this.impliedInitNameVec.addElement(name);
        } else if (level == 3)
        {
            this.impliedTemporalVec.addElement(new Action(Spec.addSubsts(pred, subs), c));
            this.impliedTemporalNameVec.addElement(name);
        } else
        {
            Assert.fail(EC.TLC_CONFIG_PROPERTY_NOT_CORRECTLY_DEFINED, name);
        }
    }

    private final Hashtable makeConstantTable(Vect consts)
    {
        Hashtable constTbl = new Hashtable();
        for (int i = 0; i < consts.size(); i++)
        {
            Vect line = (Vect) consts.elementAt(i);
            int len = line.size();
            String name = (String) line.elementAt(0);
            if (len <= 2)
            {
                constTbl.put(name, line.elementAt(1));
            } else
            {
                Object val = constTbl.get(name);
                if (val == null)
                {
                    OpRcdValue opVal = new OpRcdValue();
                    opVal.addLine(line);
                    constTbl.put(name, opVal);
                } else
                {
                    OpRcdValue opVal = (OpRcdValue) val;
                    int arity = ((Value[]) opVal.domain.elementAt(0)).length;
                    if (len != arity + 2)
                    {
                        Assert.fail(EC.TLC_CONFIG_OP_ARITY_INCONSISTENT, name);
                    }
                    opVal.addLine(line);
                }
            }
        }
        return constTbl;
    }

    /** 
     * Initialize the spec constants using the config file.  
     */
    public final Hashtable initializeConstants()
    {
        Vect consts = this.config.getConstants();
        if (consts == null)
        {
            return new Hashtable();
        }
        return this.makeConstantTable(consts);
    }

    public final Hashtable initializeModConstants()
    {
        Hashtable modConstants = this.config.getModConstants();
        Hashtable constants = new Hashtable();
        Enumeration mods = modConstants.keys();
        while (mods.hasMoreElements())
        {
            String modName = (String) mods.nextElement();
            constants.put(modName, this.makeConstantTable((Vect) modConstants.get(modName)));
        }
        return constants;
    }

    /** 
     * Get model constraints.  
     */
    public final ExprNode[] getModelConstraints()
    {
        if (this.modelConstraints != null)
        {
            return this.modelConstraints;
        }
        Vect names = this.config.getConstraints();
        this.modelConstraints = new ExprNode[names.size()];
        int idx = 0;
        for (int i = 0; i < names.size(); i++)
        {
            String name = (String) names.elementAt(i);
            Object constr = this.defns.get(name);
            if (constr instanceof OpDefNode)
            {
                OpDefNode def = (OpDefNode) constr;
                if (def.getArity() != 0)
                {
                    Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[] { "constraint", name });
                }
                this.modelConstraints[idx++] = def.getBody();
            } else if (constr != null)
            {
                if (!(constr instanceof BoolValue) || !((BoolValue) constr).val)
                {
                    Assert.fail(EC.TLC_CONFIG_ID_HAS_VALUE, new String[] { "constraint", name, constr.toString() });
                }
            } else
            {
                Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "constraint", name });
            }
        }
        if (idx < this.modelConstraints.length)
        {
            ExprNode[] constrs = new ExprNode[idx];
            for (int i = 0; i < idx; i++)
            {
                constrs[i] = this.modelConstraints[i];
            }
            this.modelConstraints = constrs;
        }
        return this.modelConstraints;
    }

    /**
     * Get action constraints.  
     */
    public final ExprNode[] getActionConstraints()
    {
        if (this.actionConstraints != null)
        {
            return this.actionConstraints;
        }
        Vect names = this.config.getActionConstraints();
        this.actionConstraints = new ExprNode[names.size()];
        int idx = 0;
        for (int i = 0; i < names.size(); i++)
        {
            String name = (String) names.elementAt(i);
            Object constr = this.defns.get(name);
            if (constr instanceof OpDefNode)
            {
                OpDefNode def = (OpDefNode) constr;
                if (def.getArity() != 0)
                {
                    Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[] { "action constraint", name });
                }
                this.actionConstraints[idx++] = def.getBody();
            } else if (constr != null)
            {
                if (!(constr instanceof BoolValue) || !((BoolValue) constr).val)
                {
                    Assert.fail(EC.TLC_CONFIG_ID_HAS_VALUE,
                            new String[] { "action constraint", name, constr.toString() });
                }
            } else
            {
                Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "action constraint", name });
            }
        }
        if (idx < this.actionConstraints.length)
        {
            ExprNode[] constrs = new ExprNode[idx];
            for (int i = 0; i < idx; i++)
            {
                constrs[i] = this.actionConstraints[i];
            }
            this.actionConstraints = constrs;
        }
        return this.actionConstraints;
    }

    /* Get the initial state predicate of the specification.  */
    public final Vect getInitStateSpec()
    {
        return this.initPredVec;
    }

    /* Get the action (next state) predicate of the specification. */
    public final Action getNextStateSpec()
    {
        return this.nextPred;
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
            Assert.fail(EC.TLC_CONFIG_ID_REQUIRES_NO_ARG, new String[] { "type cinstraint", name });

        }
        return def.getBody();
    }

    public final boolean livenessIsTrue()
    {
        return this.impliedTemporals.length == 0;
    }

    /* Get the fairness condition of the specification.  */
    public final Action[] getTemporals()
    {
        return this.temporals;
    }

    public final String[] getTemporalNames()
    {
        return this.temporalNames;
    }

    /* Get the liveness checks of the specification.  */
    public final Action[] getImpliedTemporals()
    {
        return this.impliedTemporals;
    }

    public final String[] getImpliedTemporalNames()
    {
        return this.impliedTemporalNames;
    }

    /* Get the invariants of the specification. */
    public final Action[] getInvariants()
    {
        return this.invariants;
    }

    public final String[] getInvNames()
    {
        return this.invNames;
    }

    /* Get the implied-inits of the specification. */
    public final Action[] getImpliedInits()
    {
        return this.impliedInits;
    }

    public final String[] getImpliedInitNames()
    {
        return this.impliedInitNames;
    }

    /* Get the implied-actions of the specification. */
    public final Action[] getImpliedActions()
    {
        return this.impliedActions;
    }

    public final String[] getImpliedActNames()
    {
        return this.impliedActNames;
    }

    /* Get the assumptions of the specification. */
    public final ExprNode[] getAssumptions()
    {
        return this.assumptions;
    }
    
    /* Get the assumptionIsAxiom field */
    public final boolean[] getAssumptionIsAxiom() {
        return this.assumptionIsAxiom;
    }
    /**
     * This method gets the value of a symbol from the enviroment. We
     * look up in the context c, its tool object, and the state s.
     */
    public final Object lookup(SymbolNode opNode, Context c, TLCState s, boolean cutoff)
    {
        boolean isVarDecl = (opNode.getKind() == VariableDeclKind);
        Object result = c.lookup(opNode, cutoff && isVarDecl);
        if (result != null)
            return result;

        result = opNode.getToolObject(TLCGlobals.ToolId);
        if (result != null)
            return result;

        if (opNode.getKind() == UserDefinedOpKind)
        {
            result = ((OpDefNode) opNode).getBody().getToolObject(TLCGlobals.ToolId);
            if (result != null)
                return result;
        }

        result = s.lookup(opNode.getName());
        if (result != null)
            return result;
        return opNode;
    }

    public final Object lookup(SymbolNode opNode, Context c, boolean cutoff)
    {
        boolean isVarDecl = (opNode.getKind() == VariableDeclKind);
        Object result = c.lookup(opNode, cutoff && isVarDecl);
        if (result != null)
            return result;

        result = opNode.getToolObject(TLCGlobals.ToolId);
        if (result != null)
            return result;

        if (opNode.getKind() == UserDefinedOpKind)
        {
            result = ((OpDefNode) opNode).getBody().getToolObject(TLCGlobals.ToolId);
            if (result != null)
                return result;
        }
        return opNode;
    }

    public final Object getVal(ExprOrOpArgNode expr, Context c, boolean cachable)
    {
        if (expr instanceof ExprNode)
        {
            LazyValue lval = new LazyValue(expr, c);
            if (!cachable)
            {
                lval.setUncachable();
            }
            return lval;
        }
        SymbolNode opNode = ((OpArgNode) expr).getOp();
        return this.lookup(opNode, c, false);
    }

    public final Context getOpContext(OpDefNode opDef, ExprOrOpArgNode[] args, Context c, boolean cachable)
    {
        FormalParamNode[] formals = opDef.getParams();
        int alen = args.length;
        Context c1 = c;
        for (int i = 0; i < alen; i++)
        {
            Object aval = this.getVal(args[i], c, cachable);
            c1 = c1.cons(formals[i], aval);
        }
        return c1;
    }

    /**
     * Return a table containing the locations of subexpression in the
     * spec of forms x' = e and x' \in e. Warning: Current implementation
     * may not be able to find all such locations.
     */
    public final ObjLongTable getPrimedLocs()
    {
        ObjLongTable tbl = new ObjLongTable(10);
        Action act = this.getNextStateSpec();
        this.collectPrimedLocs(act.pred, act.con, tbl);
        return tbl;
    }

    public final void collectPrimedLocs(SemanticNode pred, Context c, ObjLongTable tbl)
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
                c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true));
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
                c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true));
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

    private final void collectPrimedLocsAppl(OpApplNode pred, Context c, ObjLongTable tbl)
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
        case OPCODE_eq:
        case OPCODE_in: {
            SymbolNode var = this.getPrimedVar(args[0], c, false);
            if (var != null && var.getName().getVarLoc() != -1)
            {
                tbl.put(pred.toString(), 0);
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
            tbl.put(args[1].toString(), 0);
            break;
        }
        default: {
            if (opcode == 0)
            {
                Object val = this.lookup(opNode, c, false);

                if (val instanceof OpDefNode)
                {
                    OpDefNode opDef = (OpDefNode) val;
                    // Following added by LL on 10 Apr 2010 to avoid infinite 
                    // recursion for recursive operator definitions
                    if (opDef.getInRecursive()) {
                        return ;
                    }
                    Context c1 = this.getOpContext(opDef, args, c, true);
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

    private final void collectUnchangedLocs(SemanticNode expr, Context c, ObjLongTable tbl)
    {
        if (expr instanceof OpApplNode)
        {
            OpApplNode expr1 = (OpApplNode) expr;
            SymbolNode opNode = expr1.getOperator();
            UniqueString opName = opNode.getName();
            int opcode = BuiltInOPs.getOpCode(opName);

            if (opName.getVarLoc() >= 0)
            {
                // a state variable:
                tbl.put(expr.toString(), 0);
                return;
            }

            ExprOrOpArgNode[] args = expr1.getArgs();
            if (opcode == OPCODE_tup)
            {
                // a tuple:
                for (int i = 0; i < args.length; i++)
                {
                    this.collectUnchangedLocs(args[i], c, tbl);
                }
                return;
            }

            if (opcode == 0 && args.length == 0)
            {
                // a 0-arity operator:
                Object val = this.lookup(opNode, c, false);
                if (val instanceof OpDefNode)
                {
                    this.collectUnchangedLocs(((OpDefNode) val).getBody(), c, tbl);
                    return;
                }
            }
        }
        return;
    }

    /**
     * This method only returns an approximation of the level of the
     * expression.  The "real" level is at most the return value. Adding
     * <name, ValOne> to the context means that there is no need to
     * compute level for name.
     *
     * Note that this method does not work if called on a part of an
     * EXCEPT expression.
     */
    public final int getLevelBound(SemanticNode expr, Context c)
    {
        switch (expr.getKind()) {
        case OpApplKind: {
            OpApplNode expr1 = (OpApplNode) expr;
            return this.getLevelBoundAppl(expr1, c);
        }
        case LetInKind: {
            LetInNode expr1 = (LetInNode) expr;
            OpDefNode[] letDefs = expr1.getLets();
            int letLen = letDefs.length;
            Context c1 = c;
            int level = 0;
            for (int i = 0; i < letLen; i++)
            {
                OpDefNode opDef = letDefs[i];
                level = Math.max(level, this.getLevelBound(opDef.getBody(), c1));
                c1 = c1.cons(opDef, ValOne);
            }
            return Math.max(level, this.getLevelBound(expr1.getBody(), c1));
        }
        case SubstInKind: {
            SubstInNode expr1 = (SubstInNode) expr;
            Subst[] subs = expr1.getSubsts();
            int slen = subs.length;
            Context c1 = c;
            for (int i = 0; i < slen; i++)
            {
                Subst sub = subs[i];
                c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true));
            }
            return this.getLevelBound(expr1.getBody(), c1);
        }

        // Added by LL on 13 Nov 2009 to handle theorem and assumption names.
        case APSubstInKind: {
            APSubstInNode expr1 = (APSubstInNode) expr;
            Subst[] subs = expr1.getSubsts();
            int slen = subs.length;
            Context c1 = c;
            for (int i = 0; i < slen; i++)
            {
                Subst sub = subs[i];
                c1 = c1.cons(sub.getOp(), this.getVal(sub.getExpr(), c, true));
            }
            return this.getLevelBound(expr1.getBody(), c1);
        }


            /***********************************************************************
            * LabelKind case added by LL on 13 Jun 2007.                           *
            ***********************************************************************/
        case LabelKind: {
            LabelNode expr1 = (LabelNode) expr;
            return this.getLevelBound(expr1.getBody(), c);
        }
        default: {
            return 0;
        }
        }
    }

    private final int getLevelBoundAppl(OpApplNode expr, Context c)
    {
        SymbolNode opNode = expr.getOperator();
        UniqueString opName = opNode.getName();
        int opcode = BuiltInOPs.getOpCode(opName);

        if (BuiltInOPs.isTemporal(opcode))
        {
            return 3; // Conservative estimate
        }

        if (BuiltInOPs.isAction(opcode))
        {
            return 2; // Conservative estimate
        }

        if (opcode == OPCODE_enabled)
        {
            return 1; // Conservative estimate
        }

        int level = 0;
        ExprNode[] bnds = expr.getBdedQuantBounds();
        for (int i = 0; i < bnds.length; i++)
        {
            level = Math.max(level, this.getLevelBound(bnds[i], c));
        }

        if (opcode == OPCODE_rfs)
        {
            // For recursive function, don't compute level of the function body
            // again in the recursive call.
            SymbolNode fname = expr.getUnbdedQuantSymbols()[0];
            c = c.cons(fname, ValOne);
        }

        ExprOrOpArgNode[] args = expr.getArgs();
        int alen = args.length;
        for (int i = 0; i < alen; i++)
        {
            if (args[i] != null)
            {
                level = Math.max(level, this.getLevelBound(args[i], c));
            }
        }

        if (opcode == 0)
        {
            // This operator is a user-defined operator.
            if (opName.getVarLoc() >= 0)
                return 1;

            Object val = this.lookup(opNode, c, false);
            if (val instanceof OpDefNode)
            {
                OpDefNode opDef = (OpDefNode) val;
                c = c.cons(opNode, ValOne);
                level = Math.max(level, this.getLevelBound(opDef.getBody(), c));
            } else if (val instanceof LazyValue)
            {
                LazyValue lv = (LazyValue) val;
                level = Math.max(level, this.getLevelBound(lv.expr, lv.con));
            }
        }
        return level;
    }

    public FilenameToStream getResolver()
    {
        return resolver;
    }

    /** 
     * The level of the expression according to level checking.
     * static method, does not change instance state 
     */
    public static int getLevel(LevelNode expr, Context c)
    {
        HashSet lpSet = expr.getLevelParams();
        if (lpSet.isEmpty())
            return expr.getLevel();

        int level = expr.getLevel();
        Iterator iter = lpSet.iterator();
        while (iter.hasNext())
        {
            SymbolNode param = (SymbolNode) iter.next();
            Object res = c.lookup(param, true);
            if (res != null)
            {
                if (res instanceof LazyValue)
                {
                    LazyValue lv = (LazyValue) res;
                    int plevel = getLevel((LevelNode) lv.expr, lv.con);
                    level = (plevel > level) ? plevel : level;
                } else if (res instanceof OpDefNode)
                {
                    int plevel = getLevel((LevelNode) res, c);
                    level = (plevel > level) ? plevel : level;
                }
            }
        }
        return level;
    }

    /**
     * Static method, does not change instance state
     * @param expr
     * @param subs
     * @return
     */
    private static final ExprNode addSubsts(ExprNode expr, List subs)
    {
        ExprNode res = expr;

        while (!subs.isEmpty())
        {
            SubstInNode sn = (SubstInNode) subs.car();
            res = new SubstInNode(sn.stn, sn.getSubsts(), res, sn.getInstantiatingModule(), sn.getInstantiatedModule());
            subs = subs.cdr();
        }
        return res;
    }
}
