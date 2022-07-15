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
package tlc2.tool.impl;

import java.io.File;
import java.io.Serializable;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.APSubstInNode;
import tla2sany.semantic.AssumeNode;
import tla2sany.semantic.DecimalNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.LabelNode;
import tla2sany.semantic.LetInNode;
import tla2sany.semantic.LevelConstants;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NumeralNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpArgNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.OpDefOrDeclNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.StringNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.TheoremNode;
import tlc2.TLCGlobals;
import tlc2.module.BuiltInModuleHelper;
import tlc2.module.TLCBuiltInOverrides;
import tlc2.output.EC;
import tlc2.output.MP;
import tlc2.overrides.Evaluation;
import tlc2.overrides.ITLCOverrides;
import tlc2.overrides.TLAPlusCallable;
import tlc2.overrides.TLAPlusOperator;
import tlc2.tool.Action;
import tlc2.tool.BuiltInOPs;
import tlc2.tool.Defns;
import tlc2.tool.EvalException;
import tlc2.tool.Specs;
import tlc2.tool.TLCStateMut;
import tlc2.tool.TLCStateMutExt;
import tlc2.tool.ToolGlobals;
import tlc2.tool.impl.Tool.Mode;
import tlc2.util.Context;
import tlc2.util.List;
import tlc2.util.Vect;
import tlc2.value.IBoolValue;
import tlc2.value.IValue;
import tlc2.value.ValueConstants;
import tlc2.value.impl.BoolValue;
import tlc2.value.impl.CallableValue;
import tlc2.value.impl.EvaluatingValue;
import tlc2.value.impl.IntValue;
import tlc2.value.impl.LazyValue;
import tlc2.value.impl.MethodValue;
import tlc2.value.impl.OpRcdValue;
import tlc2.value.impl.PriorityEvaluatingValue;
import tlc2.value.impl.SetEnumValue;
import tlc2.value.impl.StringValue;
import tlc2.value.impl.Value;
import util.Assert;
import util.FilenameToStream;
import util.ToolIO;
import util.UniqueString;

public class SpecProcessor implements ValueConstants, ToolGlobals {
	
    private final String rootFile; // The root file of this spec.
    private final int toolId;
    private final Defns defns; // Global definitions reachable from root
    private final ModelConfig config; // The model configuration.
    private final OpDefEvaluator opDefEvaluator;
    private final SymbolNodeValueLookupProvider symbolNodeValueLookupProvider;
    private final TLAClass tlaClass;

    private OpDeclNode[] variablesNodes; // The state variables.
    private ExternalModuleTable moduleTbl; // The external modules reachable from root
    private ModuleNode rootModule; // The root module.
    private Set<OpDefNode> processedDefs;
    private SpecObj specObj;
    private Defns snapshot;

    private Vect<Action> initPredVec; // The initial state predicate.
    private Action nextPred; // The next state predicate.
    private Action[] temporals; // Fairness specifications...
    private String[] temporalNames; // ... and their names
    private Action[] impliedTemporals; // Liveness conds to check...
    private String[] impliedTemporalNames; // ... and their names
    private Action[] invariants; // Invariants to be checked...
    private String[] invNames; // ... and their names
    private Action[] impliedInits; // Implied-inits to be checked...
    private String[] impliedInitNames; // ... and their names
    private Action[] impliedActions; // Implied-actions to be checked...
    private String[] impliedActNames; // ... and their names
    private ExprNode[] modelConstraints; // Model constraints
    private ExprNode[] actionConstraints; // Action constraints
    private ExprNode[] assumptions; // Assumpt	ions
    private boolean[] assumptionIsAxiom; // assumptionIsAxiom[i] is true iff assumptions[i]
                                           // is an AXIOM.  Added 26 May 2010 by LL
    
    private Vect<Action> invVec = new Vect<>();
    private Vect<String> invNameVec = new Vect<>();
    private Vect<Action> impliedInitVec = new Vect<>();
    private Vect<String> impliedInitNameVec = new Vect<>();
    private Vect<Action> impliedActionVec = new Vect<>();
    private Vect<String> impliedActNameVec = new Vect<>();
    private Vect<Action> temporalVec = new Vect<>();
    private Vect<String> temporalNameVec = new Vect<>();
    private Vect<Action> impliedTemporalVec = new Vect<>();
    private Vect<String> impliedTemporalNameVec = new Vect<>();
    
	public SpecProcessor(final String rootFile, final FilenameToStream resolver, final int toolId, final Defns defns,
			final ModelConfig config, final SymbolNodeValueLookupProvider snvlp, final OpDefEvaluator ode,
			final TLAClass tlaClass, Mode mode, SpecObj obj) {
		super();
		this.rootFile = rootFile;
		this.toolId = toolId;
		this.defns = defns;
		this.config = config;
		this.tlaClass = tlaClass;
		this.processedDefs = new HashSet<OpDefNode>();
        this.initPredVec = new Vect<>(5);
        this.specObj = obj;
        
        opDefEvaluator = ode;
        symbolNodeValueLookupProvider = snvlp;

		// Parse and process this spec.
		// It takes care of all overrides.
		processSpec(mode);

		snapshot = defns.snapshot();

		if (opDefEvaluator != null) {
			// Pre-evaluate all the definitions in the spec that are constants.
			processConstantDefns();
		}

	      // Finally, process the config file.
		processConfig();
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

    private final Map<ModuleNode, Map<OpDefOrDeclNode, Object>> constantDefns = new HashMap<>();
    
    public final Map<ModuleNode, Map<OpDefOrDeclNode, Object>> getConstantDefns() {
    	return constantDefns;
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
        Object val = consts[i].getToolObject(toolId);
        if (val != null && val instanceof IValue) {
		  // We do not wrap this value in a WorkerValue, because we assume that explicit
		  // initialization does not pose a problem here. This is based on the observation,
          // that val is either an atom (IValue#isAtom) or a set (of sets) of atoms (primarily
          // ModelValues).
	      ((IValue)val).initialize();
          constantDefns.computeIfAbsent(mod, key -> new HashMap<OpDefOrDeclNode, Object>()).put(consts[i], val);
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
            	Object defVal = WorkerValue.demux(opDefEvaluator, opDef.getBody());
            	opDef.setToolObject(toolId, defVal);
            	// https://github.com/tlaplus/tlaplus/issues/648
            	//
            	// Without consts[i].setTool... below, TLC re-evaluates CONSTANT definitions on
            	// every invocation.  With consts[i].setTool..., TLC caches values.  Here is the
            	// reason why consts[i].setTool... is commented:
            	//
            	// A) For "cheap" definitions such as CONSTANT N = 4, caching values makes no 
            	//    difference.
            	//
            	// B) For more expensive expressions, such as PaxosMadeSimple.tla the performance
            	//    gain is around 10%.
            	//
            	//    Quorum == {i \in SUBSET(Server) : Cardinality(i) * 2 > Cardinality(Server)}
            	//
            	//    CONSTANT Q <- Quorum
            	//    
            	// C) However, half of our user base expects the following spec to probabilistically
            	//    have 2 to 4 distinct states:
            	//
            	//    EXTENDS TLC
            	//    R == RandomElement({1,2,3})
            	//    CONSTANT C
            	//    VARIABLE x
            	//    Spec == x = 0 /\ [][x' = C]_x
            	//
            	//    CONSTANT C <- R
            	// 
            	// Therefore, we let the user decide by giving her TLC!TLCEval to wrap expressive 
            	// constant definitions when necessary:
            	//
            	//    R == TLCEval(RandomElement({1,2,3}))
            	// 
//            	consts[i].setToolObject(toolId, defVal);

            	constantDefns.computeIfAbsent(mod, key -> new HashMap<OpDefOrDeclNode, Object>()).put(opDef, defVal);
            } catch (Assert.TLCRuntimeException | EvalException e) {
              final String addendum = (e instanceof EvalException) ? "" : (" - specifically: " + e.getMessage());
              Assert.fail(EC.TLC_CONFIG_SUBSTITUTION_NON_CONSTANT,
                  new String[] { consts[i].getName().toString(), opDef.getName().toString(), addendum });
            }
          }
        }
      }

      // run for constant operator definitions
      OpDefNode[] opDefs = mod.getOpDefs();
      DEFS: for (int i = 0; i < opDefs.length; i++) {
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
          Object realDef = symbolNodeValueLookupProvider.lookup(opDef, Context.Empty, false, toolId);
          if (realDef instanceof OpDefNode) {
            opDef = (OpDefNode)realDef;
            if (symbolNodeValueLookupProvider.getLevelBound(opDef.getBody(), Context.Empty, toolId) == LevelConstants.ConstantLevel) {
              try {
                UniqueString opName = opDef.getName();
                if (isVetoed(opName)) {
                	continue DEFS;
                }
                // System.err.println(opName);
                final Object val = WorkerValue.demux(opDefEvaluator, opDef.getBody());
                opDef.setToolObject(toolId, val);
                Object def = this.defns.get(opName);
                if (def == opDef) {
					this.defns.put(opName, val);
					constantDefns.computeIfAbsent(
							opDef.hasSource() ? opDef.getSource().getOriginallyDefinedInModuleNode() : moduleNode,
							key -> new HashMap<OpDefOrDeclNode, Object>()).put(opDef, val);
                }
              }
              catch (Throwable swallow) {
				// We get here when Op fails to evaluate. e is swallowed because Op might e.g. be 
            	// Reals!Infinity from the standard module that has to be redefined iff it appears
              	// in the actual spec. Another example is TLC!TLCGet(42) that the code above 
              	// attempts to evaluate that fails with an EvalException. By definition, TLCGet
              	// is not constant. 
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

	public static final String LAZY_CONSTANT_OPERATORS = SpecProcessor.class.getName() + ".vetoed";

	private static final Set<String> vetos = new HashSet<String>(
			Arrays.asList(System.getProperty(LAZY_CONSTANT_OPERATORS, "")));

	private boolean isVetoed(final UniqueString us) {
		return vetos.contains(us.toString());
	}

    /**
     * Processes the specification and collects information to be used
     * by tools. The processing tries to use any customized module (Java
     * class) to override the corresponding TLA+ module.
     * @param mode 
     */
    // SZ Feb 20, 2009: added support for existing specObj
    private final void processSpec(final Mode mode)
    {

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
            SANY.frontEndMain(specObj, this.rootFile, ToolIO.out);
        } catch (FrontEndException e)
        {
            Assert.fail(EC.TLC_PARSING_FAILED2, e);
        }

        if (TLCGlobals.tool)
        {
            MP.printMessage(EC.TLC_SANY_END);
        }
        // The following statement moved here by LL on 11 March 2011
        MP.printMessage(EC.TLC_STARTING);

        // SZ Feb 20, 2009:
        // since failed parsing is not marked by an exception,
        // check the status of the spec
        // check if the specification has been successfully created
		if (!specObj.initErrors.isSuccess()) {
			Assert.fail(EC.TLC_PARSING_FAILED, specObj.initErrors.getErrors());
		}
		if (!specObj.parseErrors.isSuccess()) {
			Assert.fail(EC.TLC_PARSING_FAILED, specObj.parseErrors.getErrors());
		}
		if (!specObj.semanticErrors.isSuccess()) {
			Assert.fail(EC.TLC_PARSING_FAILED, specObj.semanticErrors.getErrors());
		}

        // Set the rootModule:
        this.moduleTbl = specObj.getExternalModuleTable();
        UniqueString rootName = UniqueString.uniqueStringOf(this.rootFile);
        this.rootModule = this.moduleTbl.getModuleNode(rootName);
        
		Assert.check(this.rootModule != null, EC.TLC_PARSING_FAILED2,
				String.format(" Module-Table lookup failure for module name %s derived from %s file name.",
						rootName.toString(), this.rootFile));

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
        this.defns.put("TRUE", BoolValue.ValTrue);
        this.defns.put("FALSE", BoolValue.ValFalse);
        Value[] elems = new Value[2];
        elems[0] = BoolValue.ValFalse;
        elems[1] = BoolValue.ValTrue;
        this.defns.put("BOOLEAN", new SetEnumValue(elems, true));

        Class<?> stringModule = this.tlaClass.loadClass("Strings");
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
				// Bytecode modification (e.g. by code coverage
				// tools/aspectj/...) might have added synthetic members.
				// Synthetic members are generated by the compiler and thus
				// should not be accessed by application code. Thus, exclude
				// synthetic members from being processed.
                if (!ms[i].isSynthetic()) {
                	this.defns.put(name, MethodValue.get(ms[i]));
                }
            }
        }

        // Process all the constants in the spec. Note that this must be done
        // here since we use defns. Things added into defns later will make it
        // wrong to use it in the method processConstants.
        ModuleNode[] mods = this.moduleTbl.getModuleNodes();
        final Map<String, ModuleNode> modSet = new HashMap<String, ModuleNode>();
        for (int i = 0; i < mods.length; i++)
        {
            this.processConstants(mods[i]);
            modSet.put(mods[i].getName().toString(), mods[i]);
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
            rootConsts[i].setToolObject(toolId, val);
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
                rootOpDefs[i].setToolObject(toolId, val);
                this.defns.put(name, val);
            }
        }

        // Apply config file module specific constants to operator defns.
        // We do not allow this kind of replacement for constant decls.
        Hashtable<String, Hashtable> modConstants = this.initializeModConstants();
        for (int i = 0; i < mods.length; i++)
        {
            UniqueString modName = mods[i].getName();
            Hashtable mConsts = modConstants.get(modName.toString());
            if (mConsts != null)
            {
                OpDefNode[] opDefs = mods[i].getOpDefs();
                for (int j = 0; j < opDefs.length; j++)
                {
                    UniqueString name = opDefs[j].getName();
                    Object val = mConsts.get(name.toString());
                    if (val != null)
                    {
                        opDefs[j].getBody().setToolObject(toolId, val);
                    }
                }
            }
        }

        // Apply module overrides:
        for (int i = 0; i < mods.length; i++)
        {
        	
        	final UniqueString modName = mods[i].getName();
            final Class<?> userModule = this.tlaClass.loadClass(modName.toString());
            if (userModule != null)
            {
            	final Map<UniqueString, Integer> opname2arity = new HashMap<>();
            	if (!BuiltInModuleHelper.isBuiltInModule(userModule)) {
					// Remember arity for non built-in overrides to later match with java override
					// when loading.
            		for (OpDefNode opDefNode : rootOpDefs) {
            			if (opDefNode.getOriginallyDefinedInModuleNode().getName().equals(modName)) {
            				opname2arity.put(opDefNode.getName(), opDefNode.getArity());
            			}
            		}
            	}
                // Override with a user defined Java class for the TLA+ module.
                // Collects new definitions:
                final Hashtable<UniqueString, IValue> javaDefs = new Hashtable<UniqueString, IValue>();
                final Method[] mds = userModule.getDeclaredMethods();
                for (int j = 0; j < mds.length; j++)
                {
                	final Method method = mds[j];
                    int mdf = method.getModifiers();
                    if (Modifier.isPublic(mdf) && Modifier.isStatic(mdf))
                    {
                        String name = TLARegistry.mapName(method.getName());
                        UniqueString uname = UniqueString.uniqueStringOf(name);
						if (method.getAnnotation(TLAPlusOperator.class) != null
								|| method.getAnnotation(Evaluation.class) != null) {
							// Skip, handled below with annotation based mechanism.
							continue;
						}
                    	final int acnt = method.getParameterCount();
                    	final Value val = MethodValue.get(method);
                        
                        if (!BuiltInModuleHelper.isBuiltInModule(userModule)) {
                    		final URL resource = userModule.getResource(userModule.getSimpleName() + ".class");
                    		// Print success or failure of loading the module override (arity mismatch).
							final Integer arity = opname2arity.get(uname);
							if (arity == null || arity != acnt) {
								MP.printWarning(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MISMATCH, uname.toString(),
										resource.toExternalForm(), val.toString());
							} else {
		                        javaDefs.put(uname, val);
								MP.printMessage(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_LOADED, uname.toString(),
										resource.toExternalForm(), val.toString());
							}
                        } else {
                            javaDefs.put(uname, val);
                        }
                    }
                }
                // Adds/overrides new definitions:
                //TODO This loop could be merged with the previous loop
                // by using mods[i].getOpDef(UniqueString) right away
                // without javaDefns.
                OpDefNode[] opDefs = mods[i].getOpDefs();
                for (int j = 0; j < opDefs.length; j++)
                {
                    UniqueString uname = opDefs[j].getName();
                    Object val = javaDefs.get(uname);
                    if (val != null)
                    {
                        opDefs[j].getBody().setToolObject(toolId, val);
                        this.defns.put(uname, val);
                    }
                }
            }
        }
		// Load override definitions through user-provided index class. In other words,
		// a user creates a class that implements the interface ITLCOverrides.
		// ITLCOverride defines a single method that returns an array of classes which
		// define Java overrides (this approach is simpler and faster than scanning
		// the complete classpath). To load user-provided index classes, pass the
        // -Dtlc2.overrides.TLCOverrides property with a list of index classes
        // separated by the system's path separator (":", ";").  If no property is given,
        // the default is to load the first class on the classpath with name tlc2.overrides.TLCOverrides
        // that implements tlc2.overrides.ITLCOverrides.  This is usually the tlc2.overrides.TLCOverrides
        // provided by the CommunityModules.
        boolean hasCallableValue = false;
		final String tlcOverrides = TLCBuiltInOverrides.class.getName() + File.pathSeparator
				+ System.getProperty("tlc2.overrides.TLCOverrides", "tlc2.overrides.TLCOverrides");
		for (String ovrde : tlcOverrides.split(File.pathSeparator)) {
			final Class<?> idx = this.tlaClass.loadClass(ovrde);
			if (idx != null && ITLCOverrides.class.isAssignableFrom(idx)) {
				try {
					final ITLCOverrides index = (ITLCOverrides) idx.newInstance();
					final Class<?>[] candidateClasses = index.get();
					for (Class<?> c : candidateClasses) {
						final Method[] candidateMethods = c.getDeclaredMethods();
						LOOP: for (Method m : candidateMethods) {
							
							
							final Evaluation evaluation = m.getAnnotation(Evaluation.class);
							if (evaluation != null) {
								final ModuleNode moduleNode = modSet.get(evaluation.module());
								if (moduleNode == null) {
									if (evaluation.warn()) MP.printMessage(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MODULE_MISMATCH,
											evaluation.module() + "!" + evaluation.definition(),
											c.getResource(c.getSimpleName() + ".class").toExternalForm(), "<Java Method: " + m + ">");
									continue LOOP;
								}
								final OpDefNode opDef = moduleNode.getOpDef(evaluation.definition());
								if (opDef == null) {
									if (evaluation.warn()) MP.printMessage(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_IDENTIFIER_MISMATCH,
											evaluation.module() + "!" + evaluation.definition(),
											c.getResource(c.getSimpleName() + ".class").toExternalForm(), "<Java Method: " + m + ">");
									continue LOOP;
								}
								
								// Either load the first EvaluatingValue or combine multiple EvaluatingValues for this operator into
								// a PriorityEvaluatingValue that -given by the EVs priority- keeps evaluating every EV until one returns
								// a Value.
								final Object toolObject = opDef.getBody().getToolObject(toolId);
								if (toolObject instanceof EvaluatingValue) {
									final Value val = new PriorityEvaluatingValue(m, evaluation.minLevel(), evaluation.priority(), opDef, (EvaluatingValue) toolObject);
									opDef.getBody().setToolObject(toolId, val);
				                    this.defns.put(evaluation.definition(), val);
								} else if (toolObject instanceof PriorityEvaluatingValue) {
									final PriorityEvaluatingValue mev = (PriorityEvaluatingValue) toolObject;
									mev.add(new EvaluatingValue(m, evaluation.minLevel(), evaluation.priority(), opDef));
								} else {
									final Value val = new EvaluatingValue(m, evaluation.minLevel(), evaluation.priority(), opDef);
									opDef.getBody().setToolObject(toolId, val);
				                    this.defns.put(evaluation.definition(), val);
								}
			                    
								// Print success of loading the module override.
			                    if (!evaluation.silent()) {
			                    	MP.printMessage(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_LOADED,
			                    			evaluation.module() + "!" + evaluation.definition(),
			                    			c.getResource(c.getSimpleName() + ".class").toExternalForm(), "<Java Method: " + m + ">");
			                    }
			                    
			                    // continue with next method (don't try to also load Execution annotation below).
			                    continue LOOP;
							}
							
							final TLAPlusCallable jev = m.getAnnotation(TLAPlusCallable.class);
							if (jev != null) {
								
								final ModuleNode moduleNode = modSet.get(jev.module());
								if (moduleNode == null) {
									if (jev.warn()) MP.printMessage(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MODULE_MISMATCH,
											jev.module() + "!" + jev.definition(),
											c.getResource(c.getSimpleName() + ".class").toExternalForm(), "<Java Method: " + m + ">");
									continue LOOP;
								}
								final OpDefNode opDef = moduleNode.getOpDef(jev.definition());
								if (opDef == null) {
									if (jev.warn()) MP.printMessage(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_IDENTIFIER_MISMATCH,
											jev.module() + "!" + jev.definition(),
											c.getResource(c.getSimpleName() + ".class").toExternalForm(), "<Java Method: " + m + ">");
									continue LOOP;
								}
								
								final Value val = new CallableValue(m, jev.minLevel(), opDef);
								opDef.getBody().setToolObject(toolId, val);
			                    this.defns.put(jev.definition(), val);
			                    hasCallableValue = true;
			                    
								// Print success of loading the module override.
								MP.printMessage(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_LOADED,
										jev.module() + "!" + jev.definition(),
										c.getResource(c.getSimpleName() + ".class").toExternalForm(), val.toString());
			                    
			                    // continue with next method (don't try to also load Execution annotation below).
			                    continue LOOP;
							}
							
							final TLAPlusOperator opOverrideCandidate = m.getAnnotation(TLAPlusOperator.class);
							if (opOverrideCandidate != null) {
								final ModuleNode moduleNode = modSet.get(opOverrideCandidate.module());
								if (moduleNode == null) {
									if (opOverrideCandidate.warn()) MP.printWarning(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MODULE_MISMATCH,
											opOverrideCandidate.identifier(), opOverrideCandidate.module(), m.toString());
									continue LOOP;
								}
								final OpDefNode opDef = moduleNode.getOpDef(opOverrideCandidate.identifier());
								if (opDef == null) {
									if (opOverrideCandidate.warn()) MP.printWarning(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_IDENTIFIER_MISMATCH,
											opOverrideCandidate.identifier(), opOverrideCandidate.module(), m.toString());
									continue LOOP;
								}

								final Value val = MethodValue.get(m, opOverrideCandidate.minLevel());
								if (opDef.getArity() != m.getParameterCount()) {
									if (opOverrideCandidate.warn()) MP.printWarning(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_MISMATCH,
											opDef.getName().toString(), c.getName(), val.toString());
									continue LOOP;
								} else {
									if (opOverrideCandidate.warn()) MP.printMessage(EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE_LOADED,
											opDef.getName().toString(), c.getName(),
											val instanceof MethodValue ? val.toString() : val.getClass().getName()); // toString of non-MethodValue instances can be expensive.
								}

								opDef.getBody().setToolObject(toolId, val);
								this.defns.put(opOverrideCandidate.identifier(), val);
							}
						}
					}
				} catch (InstantiationException | IllegalAccessException e) {
					// TODO Specific error code.
					Assert.fail(EC.GENERAL);
					return;
				}
	        }
		}
        

        Set<String> overriden = new HashSet<String>();
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
                rootConsts[i].setToolObject(toolId, myVal);
                this.defns.put(lhs, myVal);
                overriden.add(lhs.toString());
            }
        }

		// set variables to the static filed in the state
		if (mode == Mode.Simulation || mode == Mode.MC_DEBUG) {
			TLCStateMutExt.setVariables(this.variablesNodes);
		} else if (hasCallableValue) {
			assert mode == Mode.Executor;
			TLCStateMutExt.setVariables(this.variablesNodes);
		} else {
			assert mode == Mode.MC;
			TLCStateMut.setVariables(this.variablesNodes);
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
                rootOpDefs[i].setToolObject(toolId, myVal);
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
        Hashtable<String, Hashtable> modOverrides = this.config.getModOverrides();
        for (int i = 0; i < mods.length; i++)
        {
            UniqueString modName = mods[i].getName();
            Hashtable mDefs = modOverrides.get(modName.toString());
            HashSet<String> modOverriden = new HashSet<>();
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
                        opDefs[j].getBody().setToolObject(toolId, myVal);
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
            if (!modSet.keySet().contains(modName))
            {
                Assert.fail(EC.TLC_NO_MODULES, modName.toString());
            }
        }
    }

    /** 
     * Process the configuration file. 
     */
    private final void processConfig()
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
        Vect<String> propNames = this.config.getProperties();
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
            } else if (!(prop instanceof IBoolValue) || !(((BoolValue) prop).val))
            {
                Assert.fail(EC.TLC_CONFIG_ID_HAS_VALUE, new String[] { "property", propName, prop.toString() });
            }
        }

        // Postprocess:
        this.invariants = new Action[this.invVec.size()];
        this.invNames = new String[this.invVec.size()];
        for (int i = 0; i < this.invVec.size(); i++)
        {
            this.invariants[i] = (Action) this.invVec.elementAt(i);
            this.invNames[i] = (String) this.invNameVec.elementAt(i);
        }

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
        
        
		// Process overrides given by ParameterizedSpecObj *after* the ordinary config
		// has been processed. A check above expects this.invariants to be empty if
		// this.initPred is empty.
        final java.util.List<Action> overrides = specObj.getInvariants();

        final ArrayList<Action> a = new ArrayList<>(Arrays.asList(this.invariants));
		a.addAll(overrides);
        this.invariants = a.toArray(Action[]::new);

        final ArrayList<String> b = new ArrayList<>(Arrays.asList(this.invNames));
        b.addAll(overrides.stream().map(act -> act.getNameOfDefault()).collect(Collectors.toList()));
        this.invNames = b.toArray(String[]::new);
        
		// Process the model constraints in the config. It's done after all
		// other config processing because it used to be processed lazy upon the
		// first invocation of getModelConstraints. However, this caused a NPE
		// in distributed mode due to concurrency issues and there was no
		// apparent reason to process the model constraints lazily.
        processModelConstraints();
        
        processActionConstraints();
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
            this.initPredVec.addElement(new Action(def.getBody(), Context.Empty, def, true, false));
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
            this.nextPred = new Action(def.getBody(), Context.Empty, def);
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
				// MK 07/25/2017: Check if the invariant is a valid state predicate and produce
				// a meaningful warning otherwise. With this enhancement, a rare bug in TLC's
				// level-checking surfaced for which we don't have a fix right now. Fortunately,
				// the bug is rather unlikely which is why TLC simply produces a warning for now
				// if it "thinks" a user might be affected by the bug.
                // see LevelNode.java line 590ff, Test52, TestInvalidInvariant, and related files
                // for more context.
                if (def.getLevel() >= 2)
                {
               		if (!def.getBody().levelParams.isEmpty()) {
                        Assert.fail(EC.TLC_INVARIANT_VIOLATED_LEVEL, new String[] { def.getName().toString(), "includeWarning" });
               		}
                	Assert.fail(EC.TLC_INVARIANT_VIOLATED_LEVEL, def.getName().toString());
                }
                this.invNameVec.addElement(name);
                this.invVec.addElement(new Action(def.getBody(), Context.Empty, def));
            } else if (inv == null)
            {
                Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "invariant", name });
            } else if (!(inv instanceof IBoolValue) || !(((BoolValue) inv).val))
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
                Object val = symbolNodeValueLookupProvider.lookup(opNode, c, false, toolId);
                if (val instanceof OpDefNode)
                {
                    if (((OpDefNode) val).getArity() != 0)
                    {
                        Assert.fail(EC.TLC_CONFIG_OP_NO_ARGS, new String[] { opNode.getName().toString() });
                    }
                    ExprNode body = ((OpDefNode) val).getBody();
                    if (symbolNodeValueLookupProvider.getLevelBound(body, c, toolId) == 1)
                    {
                        this.initPredVec.addElement(new Action(Specs.addSubsts(body, subs), c, ((OpDefNode) val), true, false));
                    } else
                    {
                        this.processConfigSpec(body, c, subs);
                    }
                } else if (val == null)
                {
                    Assert.fail(EC.TLC_CONFIG_OP_NOT_IN_SPEC, new String[] { opNode.getName().toString() });
                } else if (val instanceof IBoolValue)
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
            if ((opcode == OPCODE_te) || (opcode == OPCODE_tf))
            {
            	Assert.fail(EC.TLC_SPECIFICATION_FEATURES_TEMPORAL_QUANTIFIER);
            }
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
                if (boxArg instanceof OpApplNode) {
                	// TLC cannot handle []S where S is a constant- or state-level formula.
                	final OpApplNode oan = (OpApplNode) boxArg;
                	if (oan.getLevel() <= LevelConstants.VariableLevel) {
                        Assert.fail(EC.TLC_LIVE_CANNOT_HANDLE_FORMULA, boxArg.toString());
                	}
                }

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
                            Vect<SymbolNode> components;

                            SubscriptCollector()
                            {
                                this.components = new Vect<>();
                            }

                            void enter(ExprNode subscript, Context c)
                            {
                                // if it's a variable, add it to the vector and return
                                SymbolNode var = symbolNodeValueLookupProvider.getVar(subscript, c, false, toolId);
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
                                    Object opDef = symbolNodeValueLookupProvider.lookup(opNode, c, false, toolId);
                                    if (opDef instanceof OpDefNode)
                                    {
                                        OpDefNode opDef1 = (OpDefNode) opDef;
                                        this.enter(opDef1.getBody(), symbolNodeValueLookupProvider.getOpContext(opDef1, args, c, false, toolId));
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
                                        c1 = c1.cons(subs[i].getOp(), symbolNodeValueLookupProvider.getVal(subs[i].getExpr(), c, false, toolId));
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

                            Vect<SymbolNode> getComponents()
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
                                c1 = c1.cons(snsubs[i].getOp(), symbolNodeValueLookupProvider.getVal(snsubs[i].getExpr(), c, false, toolId));
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
                        this.nextPred = new Action(Specs.addSubsts(arg, subs), c);
                    } else
                    {
                        Assert.fail(EC.TLC_CANT_HANDLE_TOO_MANY_NEXT_STATE_RELS);
                    }
                    // ---sm 09/06/04 >>>
                } else
                {
                    this.temporalVec.addElement(new Action(Specs.addSubsts(pred, subs), c));
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

        int level = symbolNodeValueLookupProvider.getLevelBound(pred, c, toolId);
        if (level <= 1)
        {
            this.initPredVec.addElement(new Action(Specs.addSubsts(pred, subs), c));
        } else if (level == 3)
        {
            this.temporalVec.addElement(new Action(Specs.addSubsts(pred, subs), c));
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
                Object val = symbolNodeValueLookupProvider.lookup(opNode, c, false, toolId);
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
                } else if (val instanceof IBoolValue)
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
                    this.impliedActionVec.addElement(new Action(Specs.addSubsts(boxArg, subs), c));
                } else if (symbolNodeValueLookupProvider.getLevelBound(boxArg, c, toolId) < 2)
                {
                    this.invVec.addElement(new Action(Specs.addSubsts(boxArg, subs), c));
                    if ((boxArg instanceof OpApplNode) && (((OpApplNode) boxArg).getArgs().length == 0))
                    {
                        name = ((OpApplNode) boxArg).getOperator().getName().toString();
                    }
                    this.invNameVec.addElement(name);
                } else
                {
                    this.impliedTemporalVec.addElement(new Action(Specs.addSubsts(pred, subs), c));
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
        int level = symbolNodeValueLookupProvider.getLevelBound(pred, c, toolId);
        if (level <= 1)
        {
            this.impliedInitVec.addElement(new Action(Specs.addSubsts(pred, subs), c));
            this.impliedInitNameVec.addElement(name);
        } else if (level == 3)
        {
            this.impliedTemporalVec.addElement(new Action(Specs.addSubsts(pred, subs), c));
            this.impliedTemporalNameVec.addElement(name);
        } else
        {
            Assert.fail(EC.TLC_CONFIG_PROPERTY_NOT_CORRECTLY_DEFINED, name);
        }
    }
    
	private void processActionConstraints() {
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
	            final ExprNode body = def.getBody();
				// Remember OpDefNode of body because CostModelCreator needs it to correctly
				// report state statistics (CostModelCreator#create will later replace it
	            // with an Action instance).
	            assert body.getToolObject(toolId) == null;
	            body.setToolObject(toolId, def);
	            this.actionConstraints[idx++] = body;
	        } else if (constr != null)
	        {
	            if (!(constr instanceof IBoolValue) || !((BoolValue) constr).val)
	            {
	                Assert.fail(EC.TLC_CONFIG_ID_HAS_VALUE,
	                        new String[] { "action constraint", name, constr.toString() });
	            }
	        } else
	        {
	            Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "action constraint", name });
	        }
	    }
	    // Shrink in case array has been overallocated
	    if (idx < this.actionConstraints.length)
	    {
	        ExprNode[] constrs = new ExprNode[idx];
	        for (int i = 0; i < idx; i++)
	        {
	            constrs[i] = this.actionConstraints[i];
	        }
	        this.actionConstraints = constrs;
	    }
	}
    
	private final void processModelConstraints() {
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
	            final ExprNode body = def.getBody();
				// Remember OpDefNode of body because CostModelCreator needs it to correctly
				// report state statistics (CostModelCreator#create will later replace it
	            // with an Action instance).
	            assert body.getToolObject(toolId) == null;
	            body.setToolObject(toolId, def);
				this.modelConstraints[idx++] = body;
	        } else if (constr != null)
	        {
	            if (!(constr instanceof IBoolValue) || !((BoolValue) constr).val)
	            {
	                Assert.fail(EC.TLC_CONFIG_ID_HAS_VALUE, new String[] { "constraint", name, constr.toString() });
	            }
	        } else
	        {
	            Assert.fail(EC.TLC_CONFIG_SPECIFIED_NOT_DEFINED, new String[] { "constraint", name });
	        }
	    }
		// Shrink modelContraints in case we allocated a too large array. See
		// nested if block above for why some constraints don't get instantiated.
	    if (idx < this.modelConstraints.length)
	    {
	        ExprNode[] constrs = new ExprNode[idx];
	        for (int i = 0; i < idx; i++)
	        {
	            constrs[i] = this.modelConstraints[i];
	        }
	        this.modelConstraints = constrs;
	    }
	}
	 
    /*************************************************************************
     * The following method goes through all the nodes to set their           *
     * tool-specific fields.  It was modified on 1 May 2007 so it would find  *
     * the nodes in the body of a Lambda expression.  Obviously, if new       *
     * semantic node types are added, this method will have to be modified.   *
     * Less obviously, if a tool wants to call TLC on a specification that    *
     * was not all created inside a module, then this method may need to be   *
     * modified so TLC finds those nodes not part of the module.              *
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
                Object def = opDefs[i].getToolObject(toolId);
                if (def instanceof OpDefNode)
                {
                	this.processedDefs.add((OpDefNode) def);
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
                opNode.setToolObject(toolId, val);
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
            // LL added this test on 20 Jul 2011; otherwise
            // TLC treats a number bigger than MAX_VALUE 
            // (2^31-1 or 2,147,483,647) as if it equals 0.
            if (expr1.bigVal() != null) {
            	Assert.fail(EC.TLC_INTEGER_TOO_BIG, expr1.toString());
                return;
            }
            expr1.setToolObject(toolId, val);
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
            expr1.setToolObject(toolId, val);
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
            {   OpDefNode opdef = (OpDefNode) opArgNode ;
                if (! processedDefs.contains(opdef)) {
                	processedDefs.add(opdef) ;
                	this.processConstants(opdef.getBody());
                }
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

    private final Hashtable<String, Serializable> makeConstantTable(Vect<Vect<String>> consts)
    {
        Hashtable<String, Serializable> constTbl = new Hashtable<>();
        for (int i = 0; i < consts.size(); i++)
        {
            Vect<String> line = (Vect<String>) consts.elementAt(i);
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
                    int arity = ((IValue[]) opVal.domain.elementAt(0)).length;
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
    private final Hashtable initializeConstants()
    {
        Vect<Vect<String>> consts = this.config.getConstants();
        if (consts == null)
        {
            return new Hashtable<>();
        }
        return this.makeConstantTable(consts);
    }

    private final Hashtable<String, Hashtable> initializeModConstants()
    {
        Hashtable<String, ?> modConstants = this.config.getModConstants();
        Hashtable<String, Hashtable> constants = new Hashtable<>();
        Enumeration<String> mods = modConstants.keys();
        while (mods.hasMoreElements())
        {
            String modName = mods.nextElement();
            constants.put(modName, this.makeConstantTable((Vect<Vect<String>>) modConstants.get(modName)));
        }
        return constants;
    }

	public ModuleNode getRootModule() {
		return rootModule;
	}

	public ExternalModuleTable getModuleTbl() {
		return moduleTbl;
	}

	public OpDeclNode[] getVariablesNodes() {
		return variablesNodes;
	}
	
	public Vect<Action> getInitPred() {
		return initPredVec;
	}

	public Action getNextPred() {
		return nextPred;
	}

	public Action[] getTemporal() {
		return temporals;
	}

	public String[] getTemporalNames() {
		return temporalNames;
	}

	public Action[] getImpliedTemporals() {
		return impliedTemporals;
	}

	public String[] getImpliedTemporalNames() {
		return impliedTemporalNames;
	}

	public Action[] getInvariants() {
		return invariants;
	}

	public String[] getInvariantsNames() {
		return invNames;
	}

	public Action[] getImpliedInits() {
		return impliedInits;
	}

	public String[] getImpliedInitNames() {
		return impliedInitNames;
	}

	public Action[] getImpliedActions() {
		return impliedActions;
	}

	public String[] getImpliedActionNames() {
		return impliedActNames;
	}

	public ExprNode[] getModelConstraints() {
		return modelConstraints;
	}

	public ExprNode[] getActionConstraints() {
		return actionConstraints;
	}

	public ExprNode[] getAssumptions() {
		return assumptions;
	}

	public boolean[] getAssumptionIsAxiom() {
		return assumptionIsAxiom;
	}

	public SpecObj getSpecObj() {
		return specObj;
	}

	public Defns getUnprocessedDefns() {
		return snapshot;
	}
	
	public Defns getDefns() {
		return defns;
	}

	public java.util.List<ExprNode> getPostConditionSpecs() {
		return this.specObj.getPostConditionSpecs();
	}
}
