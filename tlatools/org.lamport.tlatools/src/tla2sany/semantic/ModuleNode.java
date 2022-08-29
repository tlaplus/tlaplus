// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// Last modified on Sat 21 February 2009 at 10:40:02 PST by lamport

/***************************************************************************
 * Note: This class must be modified to handle assumptions and theorems     *
 * that are ASSUME/PROVEs.  A simple way to do do this is to add new        *
 * fields to hold those ASSUME/PROVE assumptions and theorems.  This would  *
 * eliminate the need to modify TLC to test for such assumptions.           *
 ***************************************************************************/

package tla2sany.semantic;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.semantic.Context.Pair;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.xml.SymbolContext;
import util.UniqueString;
import util.WrongInvocationException;

import java.util.*;
import java.util.stream.Stream;

public class ModuleNode extends SymbolNode {

    /***********************************************************************
     * Seems to contains OpDefNodes and ThmOrAssumpDefNodes, including      *
     * ones produced by:                                                    *
     *                                                                      *
     *  - Definitions inside LETs.                                          *
     *                                                                      *
     *  - named theorems and assumptions                                    *
     *                                                                      *
     *  - ones constructed for imported definitions from top-level          *
     *    INSTANCE ... and foo == INSTANCE ... statements, but              *
     *    NOT from such statements in LETs.                                 *
     *                                                                      *
     * It does NOT contain OpDefNodes of ModuleInstanceKind that represent  *
     * a definition of the form foo == INSTANCE ...                         *
     *                                                                      *
     * It also contains ModuleNodes for inner modules, but not for modules  *
     * nested within them.                                                  *
     *                                                                      *
     * It appears that this field is never used in SANY1; it is used by the *
     * MCParser though.                                                     *
     ***********************************************************************/

    final ArrayList<OpDefNode> recursiveDecls = new ArrayList<>(8);
    // The (flat) context with all names known in this module, including
    // builtin ops, and ops declared as CONSTANT or VARIABLE, ops
    // imported and made visible via EXTENDS, and ops created through
    // INSTANCE, names from modules outer to this one, as well as the
    // names of internal modules (but not names declared or defined in
    // internal modules of this one).

    // It does NOT include ops declared or defined in internal modules,
    // ops defined in LETs, local from modules EXTENDed or INSTANCEd,
    // formal params, nor names bound by quantifier, CHOOSE, or recursive
    // function definition.
    /***********************************************************************
     * Contains the list of OpDefNode objects created by processing         *
     * RECURSIVE statements, in the order in which they were created.       *
     ***********************************************************************/

    final ArrayList<OpDefNode> opDefsInRecursiveSection = new ArrayList<>(16);
    // Modules directly extended by this one.
    /***********************************************************************
     * A ArrayList containing all the entries in the preceding three ArrayLists,  *
     * plus all top-level UseOrHideNode nodes, in the order in which they   *
     * appear in the module.                                                *
     ***********************************************************************/

    final ArrayList<OpDefNode> recursiveOpDefNodes = new ArrayList<>();
    /***************************************************************************
     * The following are the public methods of a ModuleNode object that might   *
     * be useful to a tool.                                                     *
     *                                                                          *
     * public final Context getContext() { return this.ctxt; }                  *
     *    The (flat) context with all names known in this module, including     *
     *    builtin ops, and ops declared as CONSTANT or VARIABLE, ops imported   *
     *    and made visible via EXTENDS, and ops created through INSTANCE,       *
     *    names from modules outer to this one, as well as the names of         *
     *    internal modules (but not names declared or defined in internal       *
     *    modules of this one).                                                 *
     *                                                                          *
     *    It does NOT include ops declared or defined in internal modules, ops  *
     *    defined in LETs, local from modules EXTENDed or INSTANCEd, formal     *
     *    params, nor names bound by quantifier, CHOOSE, or recursive function  *
     *    definition.                                                           *
     *                                                                          *
     * public final OpDeclNode[] getConstantDecls() {                           *
     *    Returns ArrayList of the OpDeclNode's in the current module              *
     *    representing CONSTANT declarations, including operator constants      *
     *    and constants defined via EXTENDS and INSTANCE, but excluding         *
     *    CONSTANTS from internal modules.                                      *
     *                                                                          *
     * public final OpDeclNode[] getVariableDecls() {                           *
     *    Returns a ArrayList of the OpDeclNode's in the current module            *
     *    representing VARIABLE declarations, including those defined via       *
     *    EXTENDS and INSTANCE, but excluding VARIABLES from internal modules.  *
     *                                                                          *
     * public final OpDefNode[] getOpDefs() {                                   *
     *    Returns array of the OpDefNode's created in the current module,       *
     *    including function defs, and operators those defined via EXTENDS      *
     *    and INSTANCE, but excluding built-in operators, operators in the      *
     *    LET-clause of a let-expression, formal parameters, bound variables,   *
     *    and operators defined in internal modules.                            *
     *    The OpDefNodes are ordered such that if B is defined in terms of A,   *
     *    then B has a HIGHER index than A in the returned array.               *
     *                                                                          *
     * public final ThmOrAssumpDefNode[] getThmOrAssDefs() {                    *
     *    Returns an array of all ThmOrAssumpDefNode objects created in the     *
     *    current module (but not in inner modules).  They should appear in     *
     *    the order in which they occur in the module.  Code copied from        *
     *    getOpDefs().                                                          *
     *                                                                          *
     * public final void appendDef(SemanticNode s) {                            *
     *    Appends to ArrayList of definitions in this module; should only be       *
     *    called with AssumeNodes, ModuleNodes, OpDefNodes and TheoremNodes as  *
     *    arguments.                                                            *
     *                                                                          *
     * public final InstanceNode[] getInstances() {                             *
     *    Returns array of the InstanceNode's representing module               *
     *    instantiations in the current module, including those inherited via   *
     *    EXTENDS, but excluding those in the LET-clause of a let-expression    *
     *    and in internal modules                                               *
     *                                                                          *
     * public final void appendInstance(InstanceNode s) {                       *
     *    Appends to ArrayList of instantiations in this module                    *
     *                                                                          *
     * public final ModuleNode[] getInnerModules() {                            *
     *    Returns an array of all the top-level inner modules that appear in    *
     *    this module.  Their submodules in turn are retrieved by again         *
     *    applying this method to the ModuleNode's in the returned ArrayList,      *
     *    etc.                                                                  *
     *                                                                          *
     * public final AssumeNode[] getAssumptions() {                             *
     *    Returns the array of AssumeNodes that are part of this module.  It    *
     *    includes assumptions from extended but not instantiated modules.      *
     *                                                                          *
     * public final TheoremNode[] getTheorems() {                               *
     *    Returns the array of TheoremNodes that are part of this module.  It   *
     *    includes theorems from extended but not instantiated modules.         *
     *                                                                          *
     * public final LevelNode[] getTopLevel() {                                 *
     *    Returns the array of TheoremNodes, AssumeNodes, top-level             *
     *    InstanceNodes, and top-level UseOrHideNodes, in the order in which    *
     *    the corresponding statements appeared in the module.                  *
     *                                                                          *
     * public final boolean isConstant() {                                      *
     *    It is not a constant module iff it contains any VARIABLE              *
     *    declarations or non-constant operators.                               *
     *                                                                          *
     * public final HashSet getExtendedModuleSet() {                            *
     *    Returns a hashset whose elements are ModuleNode objects representing  *
     *    all modules that are extended by this module--either directly or      *
     *    indirectly.                                                           *
     *                                                                          *
     * public boolean extendsModule(ModuleNode mod)                             *
     *    Returns true iff this module extends module mod--either directly or   *
     *    indirectly.                                                           *
     *                                                                          *
     * The following methods are not implememted.  The first two require work   *
     * to implement them.  Implementing the third is trivial.                   *
     *                                                                          *
     * public final TheoremNode[] getThms() { return null; }                    *
     *    Returns an array of all the theorems that appear in this module,      *
     *    along with their proofs (if they have them).  It includes theorems    *
     *    obtained from extended and instantiated modules.  Note that if        *
     *    module M has ASSUME statements A and B, then                          *
     *                                                                          *
     *       Foo(x, y) == INSTANCE M WITH ...                                   *
     *                                                                          *
     *    introduces, for each theorem T in module M, the theorem               *
     *                                                                          *
     *       ASSUME 1. LEVELDECL x                                              *
     *              2. LEVELDECL y                                              *
     *              3. A                                                        *
     *              4. B                                                        *
     *       PROVE  T                                                           *
     *                                                                          *
     *    where LEVELDECL denotes some appropriate level declaration based on   *
     *    the maximum levels of expressions that can be substituted for the     *
     *    formal parameters x and y.                                            *
     *                                                                          *
     *    This was written when we planned to allow a PROVE to contain an       *
     *    ASSUME/PROVE.  Since it can't, the ASSUMEs of the theorem would       *
     *    have to be added to the ASSUME list.                                  *
     *                                                                          *
     * public final AssumeProveNode[] getAssumes() { return null; }             *
     *    Returns an array of all the assumptions (the expressions in ASSUME    *
     *    statements).                                                          *
     *                                                                          *
     *    This was written when we planned to allow the body of an ASSUME       *
     *    statement to be an ASSUME/PROVE. Since it can't, this would return    *
     *    an ExprNode[] array.                                                  *
     ***************************************************************************/

    private final Context ctxt;
    // CONSTANTs declared in this module
    /***********************************************************************
     * This is set by createExtendeeArray, which is called by               *
     * Generator.processExtendsList.  However, its value does not seem to   *
     * be used anywhere, nor is it made available to users of the           *
     * ModuleNode class.                                                    *
     ***********************************************************************/

    private final HashMap<Boolean, HashSet<ModuleNode>> depthAllExtendeesMap = new HashMap<>();
    // VARIABLEs declared in this module
    private final ArrayList<SemanticNode> definitions = new ArrayList<>();
    // AssumeNodes, internal ModuleNodes, OpDefNodes, and TheoremNodes, in
    // the exact order they were defined in this module
    /*************************************************************************
     * The next three ArrayLists hold the ASSUMEs, THEOREMs, and top-level       *
     * INSTANCEs (ones not in LETs) declared in this module or inherited via  *
     * EXTENDS, in the order in which they appear in the module.              *
     *                                                                        *
     * A tool that wants to find all the ASSUMEs and THEOREMs that are        *
     * inherited via INSTANCing must gather them from instanceVec.  However,  *
     * new ThmOrAssumpDefNode objects are added to the module for all         *
     * instantiated named theorems and assumptions.  A tool that needs to     *
     * associate this ThmOrAssumpDefNode with the instantiated theorem or     *
     * assumption needs to look up the instantiated theorem name (e.g.,       *
     * Inst!Foo!Thm).  I believe that to look up a name with UniqueString     *
     * uniquestr in ModuleNode mn, one calls                                  *
     * mn.getContext().getSymbol(uniquestr).                                  *
     *************************************************************************/
    private final ArrayList<AssumeNode> assumptionVec = new ArrayList<>();  // ArrayList of AssumeNodes
    private final ArrayList<TheoremNode> theoremVec = new ArrayList<>();  // ArrayList of TheoremNodes
    private final ArrayList<InstanceNode> instanceVec = new ArrayList<>();  // ArrayList of InstanceNodes
    private final ArrayList<LevelNode> topLevelVec = new ArrayList<>();
    /***********************************************************************
     * The list of all OpDefNode objects opd in this module, and in any     *
     * inner modules, with opd.recursiveSection >= 0.  (See the comments    *
     * for OpDefNode.recursiveSection to see what this field means.)        *
     ***********************************************************************/

    int nestingLevel;
    private ModuleNode[] extendees = new ModuleNode[0];
    /***********************************************************************
     * The set of all modules that are extended by this module--either      *
     * directly or indirectly, keyed a Boolean representing whether the     *
     * extendees are gathered recursively of not.                           *
     * Returned by getExtendModules                                         *
     ***********************************************************************/

    private OpDeclNode[] constantDecls = null;
    private OpDeclNode[] variableDecls = null;
    /***********************************************************************
     * The number of outer modules within which this module occurs.  It     *
     * equals 0 for an outer-level module; it equals 1 for a module whose   *
     * "----- MODULE" token is at the outer level of an outer-level         *
     * module, and so on.                                                   *
     ***********************************************************************/

    private OpDefNode[] opDefs = null;
    // operators defined in this module, in order defined
    private ThmOrAssumpDefNode[] thmOrAssDefs = null;
    // theorems or assumptions defined in this module, in order defined
    private ModuleNode[] modDefs = null;
    // inner modules defined in this module
    private InstanceNode[] instantiations = null;
    /***********************************************************************
     * True iff this module is a standard module.  It is set in the SANY    *
     * class's frontEndSemanticAnalysis method after the ModuleNode object  *
     * is created.  It is apparently not set for a module nested within     *
     * another module.  Therefore, it is initialized to false because no    *
     * standard module has an inner module.                                 *
     *                                                                      *
     * It is possible that this field is never set when the parser is       *
     * called by distributed TLC.                                           *
     ***********************************************************************/

    /***********************************************************************
     * The "unnamed" in the comments above is meaningless, because the      *
     * semantic analysis in SANY1 never handled named theorems and          *
     * assumptions.                                                         *
     *                                                                      *
     * As of 11 Apr 2007, for a named theorem or assumption (e.g., THEOREM  *
     * foo == body), a TheoremNode for body is added to theorems and an     *
     * OpDefNode for foo is added to opDefs.                                *
     ***********************************************************************/
    // top level module instantiations in this module
    private AssumeNode[] assumptions = null;
    // assumptions in this module
    private TheoremNode[] theorems = null;
    // theorems in this module
    private LevelNode[] topLevel = null;
    /***********************************************************************
     * Theorems, assumptions, and top-level module instantiations, USEs,    *
     * and HIDEs.                                                           *
     ***********************************************************************/
    private boolean isInstantiated = false;
    /***********************************************************************
     * True iff this module is instantiated in a top-level INSTANCE         *
     * statement--that is, one not inside a proof.  It is set when          *
     * processing the INSTANCE statement in the Generator class.            *
     ***********************************************************************/

    private boolean isStandard = false;
    private SemanticNode[] children = null;

    /***********************************************************************
     * A ArrayList of all OpDefNodes for operators declared in RECURSIVE       *
     * statements--even within LET expressions.                             *
     ***********************************************************************/

    // Invoked only in Generator
    public ModuleNode(final UniqueString us, final Context ct, final TreeNode stn) {
        super(ModuleKind, stn, us);
        this.ctxt = ct;
    }

    // Required for SymbolNode interface.
    @Override
    public final int getArity() {
        return -2;
    }

    /**
     * This just returns null.  I don't know why its needed.
     */
    public final SymbolTable getSymbolTable() {
        return null;
    }

    public final Context getContext() {
        return this.ctxt;
    }

    // Meaningless--just here for compatibility with SymbolNode interface
    @Override
    public final boolean isLocal() {
        return false;
    }

    // Returns true iff this module has no parmeters, i.e. CONSTANT or
    // VARIABLE decls, so that INSTANCEing it is the same as EXTENDing it.
    final boolean isParameterFree() {
        return (getConstantDecls().length == 0 &&
                getVariableDecls().length == 0);
    }

    public List<SemanticNode> getDefinitions() {
        return definitions;
    }

    public final void createExtendeeArray(final ArrayList<ModuleNode> extendeeVec) {
        /***********************************************************************
         * This is called by Generator.processExtendsList to set the            *
         * ModuleNode's extendees field, which never seems to be used.          *
         ***********************************************************************/
        extendees = new ModuleNode[extendeeVec.size()];

        for (int i = 0; i < extendees.length; i++) {
            extendees[i] = extendeeVec.get(i);
        }
    }

    /**
     * Returns ArrayList of the OpDeclNode's in the current module
     * representing CONSTANT declarations, including operator constants
     * and constants defined via EXTENDS and INSTANCE, but excluding
     * CONSTANTS from internal modules.
     */
    public final OpDeclNode[] getConstantDecls() {
        if (constantDecls != null) return constantDecls;

        final ArrayList<SemanticNode> contextVec = ctxt.getConstantDecls();
        constantDecls = new OpDeclNode[contextVec.size()];
        for (int i = 0, j = constantDecls.length - 1; i < constantDecls.length; i++) {
            constantDecls[j--] = (OpDeclNode) contextVec.get(i);
        }
        return constantDecls;
    }

    /**
     * Returns a ArrayList of the OpDeclNode's in the current module
     * representing VARIABLE declarations, including those defined via
     * EXTENDS and INSTANCE, but excluding VARIABLES from internal modules.
     */
    public final OpDeclNode[] getVariableDecls() {
        if (variableDecls != null) return variableDecls;

        final ArrayList<SemanticNode> contextVec = ctxt.getVariableDecls();
        variableDecls = new OpDeclNode[contextVec.size()];
        for (int i = 0, j = variableDecls.length - 1; i < variableDecls.length; i++) {
            variableDecls[j--] = (OpDeclNode) contextVec.get(i);
        }
        return variableDecls;
    }

    /**
     * Returns array of the OpDefNode's created in the current module,
     * including function defs, and operators those defined via EXTENDS
     * and INSTANCE, but excluding built-in operators, operators in the
     * LET-clause of a let-expression, formal parameters, bound
     * variables, and operators defined in internal modules.
     * <p>
     * The OpDefNodes are ordered such that if B is defined in terms of
     * A, then B has a HIGHER index than A in the returned array.
     */
    public final OpDefNode[] getOpDefs() {
        if (opDefs != null) return opDefs;
        final ArrayList<OpDefNode> contextVec = ctxt.getOpDefs();
        opDefs = new OpDefNode[contextVec.size()];
        for (int i = 0, j = opDefs.length - 1; i < opDefs.length; i++) {
            opDefs[j--] = contextVec.get(i);
        }
        return opDefs;
    }

    public final OpDefNode getOpDef(final String name) {
        return getOpDef(UniqueString.uniqueStringOf(name));
    }

    public final OpDefNode getOpDef(final UniqueString name) {
        return Stream.of(getOpDefs()).filter(o -> o.getName() == name).findFirst().orElse(null);
    }

    /*************************************************************************
     * Returns an array of all ThmOrAssumpDefNode objects created in the      *
     * current module (but not in inner modules).  They should appear in the  *
     * order in which they occur in the module.  Code copied from             *
     * getOpDefs().                                                           *
     *************************************************************************/
    public final ThmOrAssumpDefNode[] getThmOrAssDefs() {
        if (thmOrAssDefs != null) return thmOrAssDefs;
        final ArrayList<ThmOrAssumpDefNode> contextVec = ctxt.getThmOrAssDefs();
        thmOrAssDefs = new ThmOrAssumpDefNode[contextVec.size()];
        for (int i = 0, j = thmOrAssDefs.length - 1;
             i < thmOrAssDefs.length; i++) {
            thmOrAssDefs[j--] = contextVec.get(i);
        }
        return thmOrAssDefs;
    }

    /**
     * Appends to ArrayList of definitions in this module; should only be called with
     * AssumeNodes, ModuleNodes, OpDefNodes and TheoremNodes as arguments.
     */
    public final void appendDef(final SemanticNode s) {
        definitions.add(s);
    }

    /**
     * Returns array of the InstanceNode's representing module
     * instantiations in the current module, including those inherited
     * via EXTENDS, but excluding those in the LET-clause of a
     * let-expression and in internal modules
     */
    public final InstanceNode[] getInstances() {
        if (instantiations != null) return instantiations;

        instantiations = new InstanceNode[instanceVec.size()];
        for (int i = 0; i < instantiations.length; i++) {
            instantiations[i] = (instanceVec.get(i));
        }
        return instantiations;
    }

    /**
     * Appends to ArrayList of instantiations in this module
     */
    public final void appendInstance(final InstanceNode s) {
        instanceVec.add(s);
        topLevelVec.add(s);
    }

    /**
     * Returns an array of all the top-level inner modules that appear
     * in this module.  Their submodules in turn are retrieved by again
     * applying this method to the ModuleNode's in the returned ArrayList,
     * etc.
     */
    public final ModuleNode[] getInnerModules() {
        if (modDefs != null) return modDefs;

        final ArrayList<SemanticNode> v = ctxt.getModDefs();
        modDefs = new ModuleNode[v.size()];
        for (int i = 0; i < modDefs.length; i++) {
            modDefs[i] = (ModuleNode) v.get(i);
        }
        return modDefs;
    }

    /**
     * Returns the array of AssumeNodes that are part of this module,
     * including ones from extended (but not instantiated) modules.
     */
    public final AssumeNode[] getAssumptions() {
        if (assumptions != null) return assumptions;

        assumptions = new AssumeNode[assumptionVec.size()];
        for (int i = 0; i < assumptions.length; i++) {
            assumptions[i] = assumptionVec.get(i);
        }
        return assumptions;
    }

    /**
     * Returns the array of TheoremNodes that are part of this module,
     * including ones from extended (but not instantiated) modules.
     */
    public final TheoremNode[] getTheorems() {
        if (theorems != null) return theorems;

        theorems = new TheoremNode[theoremVec.size()];
        for (int i = 0; i < theorems.length; i++) {
            theorems[i] = (theoremVec.get(i));
        }
        return theorems;
    }

    /*************************************************************************
     * Returns the array of TheoremNodes, AssumeNodes, top-level              *
     * InstanceNodes, and top-level UseOrHideNodes, in the order in which     *
     * the corresponding statements appeared in the module.                   *
     *************************************************************************/
    public final LevelNode[] getTopLevel() {
        if (topLevel != null) return topLevel;

        topLevel = new LevelNode[topLevelVec.size()];
        for (int i = 0; i < topLevel.length; i++) {
            topLevel[i] = (topLevelVec.get(i));
        }
        return topLevel;
    }

    /**
     * @return the isInstantiated
     */
    public boolean isInstantiated() {
        return isInstantiated;
    }

    /**
     * @param isInstantiated the isInstantiated to set
     */
    public void setInstantiated(final boolean isInstantiated) {
        this.isInstantiated = isInstantiated;
    }

    /**
     * @return the isStandard
     * @see tla2sany.modanalyzer.ParseUnit#isLibraryModule()
     */
    public boolean isStandard() {
        return isStandard;
    }

    /**
     * @param isStandard the isStandard to set
     * @see tla2sany.modanalyzer.ParseUnit#isLibraryModule()
     */
    public void setStandard(final boolean isStandard) {
        this.isStandard = isStandard;
    }

    final void addAssumption(final TreeNode stn, final ExprNode ass, final SymbolTable st,
                             final ThmOrAssumpDefNode tadn) {
        /***********************************************************************
         * Create a new assumption node and add it to assumptionVec and         *
         * topLevelVec.                                                         *
         ***********************************************************************/
        final AssumeNode an = new AssumeNode(stn, ass, this, tadn);
        assumptionVec.add(an);
        topLevelVec.add(an);
    }

    final void addTheorem(final TreeNode stn, final LevelNode thm, final ProofNode pf,
                          final ThmOrAssumpDefNode tadn) {
        /***********************************************************************
         * LL Change: 17 Mar 2007 - Removed localness argument because          *
         *                          theorems cannot be local                    *
         *                        - Changed thm argument to allow               *
         *                          AssumeProveNode as well as ExprNode         *
         * LL Change: 29 Jul 2007 - Add node to topLevelVec.                    *
         ***********************************************************************/
        final TheoremNode tn = new TheoremNode(stn, thm, this, pf, tadn);
        theoremVec.add(tn);
        topLevelVec.add(tn);
    }

    final void addTopLevel(final LevelNode nd) {
        topLevelVec.add(nd);
    }

    final void copyAssumes(final ModuleNode extendee) {
        assumptionVec.addAll(extendee.assumptionVec);
    }

    final void copyTheorems(final ModuleNode extendee) {
        theoremVec.addAll(extendee.theoremVec);
    }

    final void copyTopLevel(final ModuleNode extendee) {
        topLevelVec.addAll(extendee.topLevelVec);
    }

    public final HashSet<ModuleNode> getExtendedModuleSet() {
        return getExtendedModuleSet(true);
    }

    /**
     * @param recursively if true, the extendees of extendees of extendees of ...
     *                    will be included; if false, only the direct extendees
     *                    of this instance will be returned.
     */
    public final HashSet<ModuleNode> getExtendedModuleSet(final boolean recursively) {
        /***********************************************************************
         * Returns a Hashset whose elements are ModuleNode objects representing *
         * all modules that are extended by this module--either directly or     *
         * indirectly.                                                          *
         ***********************************************************************/
        final Boolean key = recursively;
        HashSet<ModuleNode> extendeesSet = depthAllExtendeesMap.get(key);
        if (extendeesSet == null) {
            extendeesSet = new HashSet<>();
            for (final ModuleNode extendee : this.extendees) {
                extendeesSet.add(extendee);
                if (recursively) {
                    extendeesSet.addAll(extendee.getExtendedModuleSet(true));
                }
            }

            depthAllExtendeesMap.put(key, extendeesSet);
        }

        return extendeesSet;
    }

    /**
     * Just a stub method; one cannot resolve against a ModuleNode.
     * This method is here only to satisfy the SymbolNode interface.
     */
    @Override
    public final boolean match(final OpApplNode sn, final ModuleNode mn) {
        return false;
    }

    /**
     * Returns an array of all the theorems that appear in this module,
     * along with their proofs (if they have them).  It includes theorems
     * obtained from extended and instantiated modules.  Note that if
     * module M has ASSUME statements A and B, then
     * <p>
     * Foo(x, y) == INSTANCE M WITH ...
     * <p>
     * introduces, for each theorem T in module M, the theorem
     * <p>
     * ASSUME 1. LEVELDECL x
     * 2. LEVELDECL y
     * 3. A
     * 4. B
     * PROVE  T
     * <p>
     * where LEVELDECL denotes some appropriate level declaration based
     * on the maximum levels of expressions that can be substituted
     * for the formal parameters x and y.
     * <p>
     * Not implemented -- see getTheorems()
     */
    public final TheoremNode[] getThms() {
        return null;
    }

    /* Level checking */
//  Old level parameter fields removed and replace by subfields
//  of levelData.

    /**
     * Returns an array of all the assumptions (the expressions in ASSUME
     * statements).  An assumption in an ordinary specification has the
     * form
     * <p>
     * ASSUME A == expr
     * <p>
     * where expr is a constant-level expression.  However, the grammar
     * allows assumptions such as
     * <p>
     * ASSUME A == ASSUME B
     * PROVE  C
     * <p>
     * Hence, an assumption must be represented by an AssumeProveNode.
     * <p>
     * An assumption like this produces a ref in getAssumes() to the
     * AssumeProveNode that represents the assumption, and a ref in
     * getOpDefs to the OpDefNode that represents the definition of A.
     * <p>
     * Not implemented -- see getAssumptions()
     */
    public final AssumeProveNode[] getAssumes() {
        return null;
    }

    @Override
    public final boolean levelCheck(final int itr) {

        if (levelChecked >= itr) return this.levelCorrect;
        levelChecked = itr;

/***************************************************************************
 * REMOVE THIS CODE XXXX                                                    *
 ***************************************************************************/
// System.out.println("Module " + this.getName() + " has level "
//                      + this.nestingLevel);
// for (int i = 0; i < definitions.size(); i++) {
// if (definitions.get(i) instanceof OpDefNode) {
// OpDefNode foo = (OpDefNode) definitions.get(i) ;
// System.out.println("definitions, module " + this.getName() + ": "
//    + foo.getName() + " rec sec: " + foo.recursiveSection) ;
// }
// else
// { System.out.println("definitions, module " + this.getName() +
//    ": non-OpDefNode "   + ((SymbolNode) definitions.get(i)).getName()) ;
// }
// };
//
// for (int i = 0; i < opDefsInRecursiveSection.size(); i++) {
// System.out.println("opDefsInRecursiveSection, module " + this.getName() + ": "
//    + ((SymbolNode) opDefsInRecursiveSection.get(i)).getName()) ;
// };

// XXXXXXX Testing

/***************************************************************************
 * Perform level checking for all operator definitions in recursive         *
 * sections.  See the explanation in the file level-checking-proposal.txt,  *
 * a copy of which is at the end of the file semantic/LevelNode.java.       *
 ***************************************************************************/
        int firstInSectIdx = 0;
        while (firstInSectIdx < opDefsInRecursiveSection.size()) {
            /*********************************************************************
             * Each iterate of this loop handles one recursive section whose      *
             * first OpDefNode is element firstInSectIdx of the                   *
             * opDefsInRecursiveSection ArrayList.                                   *
             *********************************************************************/
            int curNodeIdx = firstInSectIdx;
            OpDefNode curNode = opDefsInRecursiveSection.get(curNodeIdx);
            final int curSection = curNode.recursiveSection;
            boolean notDone = true;
            while (notDone) {
                /*******************************************************************
                 * This loop initializes the level information for the recursive    *
                 * OpDefNode objects in this section and exits when curNodeIdx      *
                 * equals either the index of the first OpDefNode in the next       *
                 * recursive section or opDefsInRecursiveSection.size() if there    *
                 * is no next section.                                              *
                 *******************************************************************/
                if (curNode.inRecursive) {
                    /*****************************************************************
                     * Specially initialize a recursive operator's level fields.      *
                     *****************************************************************/
                    curNode.levelChecked = 1;
                    for (int i = 0; i < curNode.getArity(); i++) {
                        curNode.maxLevels[i] = ActionLevel;
                        curNode.weights[i] = 1;
                    } // for;
                } // if (curNode.inRecursive)
                else {
                    curNode.levelChecked = 0;
                }
                curNodeIdx++;
                if (curNodeIdx < opDefsInRecursiveSection.size()) {
                    curNode = opDefsInRecursiveSection.get(curNodeIdx);
                    notDone = (curNode.recursiveSection == curSection);
                } else {
                    notDone = false;
                }
            }// while (notDone)


            /*********************************************************************
             * Do the level checking for each operator in the recursive section,  *
             * and set maxRecursiveLevel to the maximum level and                 *
             * recursiveLevelParams to the union of the levelParams for all       *
             * recursive operators.  Do the analogous operation for allParams,    *
             * using recursiveAllParams.                                          *
             *********************************************************************/
            int maxRecursiveLevel = ConstantLevel;
            final HashSet<SymbolNode> recursiveLevelParams = new HashSet<>();
            final HashSet<SymbolNode> recursiveAllParams = new HashSet<>();
            for (int i = firstInSectIdx; i < curNodeIdx; i++) {
                curNode = opDefsInRecursiveSection.get(i);
                if (curNode.inRecursive) {
                    curNode.levelChecked = 0;
                }
                curNode.levelCheck(1);

                if (curNode.inRecursive) {
                    /*****************************************************************
                     * For a recursive node, check for primed arguments and update    *
                     * maxRecursiveLevel, recursiveLevelParams, and                   *
                     * recursiveAllParams.                                            *
                     *****************************************************************/
                    for (int j = 0; j < curNode.getArity(); j++) {
                        if (curNode.maxLevels[j] < ActionLevel) {
                            errors.get().addError(curNode.getTreeNode().getLocation(),
                                    "Argument " + (j + 1) + " of recursive operator "
                                            + curNode.getName() + " is primed");
                        } // if
                    } // for j
                    maxRecursiveLevel = Math.max(maxRecursiveLevel, curNode.level);
                    recursiveLevelParams.addAll(curNode.levelParams);
                    recursiveAllParams.addAll(curNode.allParams);
                }// if (curNode.inRecursive)
            }// for i

            /*********************************************************************
             * Reset the level, levelParams, allParams, and levelChecked fields   *
             * for every operator in the recursive section.                       *
             *********************************************************************/
            for (int i = firstInSectIdx; i < curNodeIdx; i++) {
                curNode = opDefsInRecursiveSection.get(i);
                if (curNode.inRecursive) {
                    curNode.levelChecked = 2;
                }
                curNode.level = Math.max(curNode.level, maxRecursiveLevel);
                curNode.levelParams.addAll(recursiveLevelParams);
                curNode.allParams.addAll(recursiveAllParams);
            }// for i

            /*********************************************************************
             * Perform the level checking again on the operators in the           *
             * recursive section.                                                 *
             *********************************************************************/
            for (int i = firstInSectIdx; i < curNodeIdx; i++) {
                curNode = opDefsInRecursiveSection.get(i);
                if (curNode.inRecursive) {
                    curNode.levelChecked = 1;
                }
                curNode.levelCheck(2);
            }// for i

            firstInSectIdx = curNodeIdx;
        } // while (firstInSectIdx < ...)

        /***********************************************************************
         * We now do level checking as in SANY1 for everything in the module    *
         * that wasn't just level checked.                                      *
         ***********************************************************************/
        // Level check everything in this module
        this.levelCorrect = true;
        final ModuleNode[] mods = this.getInnerModules();
        for (final ModuleNode mod : mods) {
            if (!mod.levelCheck(1)) {
                this.levelCorrect = false;
            }
        }

        final OpDefNode[] opDefs = this.getOpDefs();
        /*********************************************************************
         * I don't understand why this is preceded by OpDefNode[],            *
         * presumably making it a local variable.  However, it doesn't seem   *
         * to make any difference, so I've left it.                           *
         *********************************************************************/
        for (final OpDefNode def : opDefs) {
            if (!def.levelCheck(1)) {
                this.levelCorrect = false;
            }
        }
        thmOrAssDefs = this.getThmOrAssDefs();
        for (final ThmOrAssumpDefNode thmOrAssDef : thmOrAssDefs) {
            if (!thmOrAssDef.levelCheck(1)) {
                this.levelCorrect = false;
            }
        }

        /***********************************************************************
         * Can use topLevel instead of the three separate arrays theorems,      *
         * assumptions, and instances.                                          *
         ***********************************************************************/
        final LevelNode[] tpLev = this.getTopLevel();
        for (final LevelNode node : tpLev) {
            if (!node.levelCheck(1)) {
                this.levelCorrect = false;
            }
        }
//    TheoremNode[] thms = this.getTheorems();
//    for (int i = 0; i < thms.length; i++) {
//// System.out.println("theorem " + i + " from module " + this.getName());
//      if (!thms[i].levelCheck(1)) {
//      this.levelCorrect = false;
//      }
//    }
//    AssumeNode[] assumps = this.getAssumptions();
//    for (int i = 0; i < assumps.length; i++) {
//// System.out.println("assumption " + i + " from module " + this.getName());
//      if (!assumps[i].levelCheck(1)) {
//      this.levelCorrect = false;
//      }
//    }
//    InstanceNode[] insts = this.getInstances();
//    for (int i = 0; i < insts.length; i++) {
//// System.out.println("instance " + i + " from module " + this.getName());
//      if (!insts[i].levelCheck(1)) {
//      this.levelCorrect = false;
//      }
//    }

        // Calculate level and Leibniz information.
//    this.levelParams = new HashSet();
        final OpDeclNode[] decls = this.getConstantDecls();
        for (final OpDeclNode opDeclNode : decls) {
            this.levelParams.add(opDeclNode);
            this.allParams.add(opDeclNode);
        }

        if (!this.isConstant()) {
            for (final OpDeclNode decl : decls) {
                this.levelConstraints.put(decl, Levels[ConstantLevel]);
            }
        }
        for (final OpDefNode opDef : opDefs) {
            this.levelConstraints.putAll(opDef.getLevelConstraints());
            this.argLevelConstraints.putAll(opDef.getArgLevelConstraints());
            for (final ArgLevelParam alp : opDef.getArgLevelParams()) {
                if (!alp.occur(opDef.getParams())) {
                    this.argLevelParams.add(alp);
                }
            }
        }

        /***********************************************************************
         * Can use topLevel instead of the three separate arrays theorems,      *
         * assumptions, and instances.                                          *
         ***********************************************************************/
        for (final LevelNode levelNode : tpLev) {
            this.levelConstraints.putAll(levelNode.getLevelConstraints());
            this.argLevelConstraints.putAll(levelNode.getArgLevelConstraints());
            this.argLevelParams.addAll(levelNode.getArgLevelParams());
        }

        return this.levelCorrect;
    }

    @Override
    public final int getLevel() {
        throw new WrongInvocationException("Internal Error: Should never call ModuleNode.getLevel()");
    }

    /**
     * Returns true iff the module is a constant module. See the
     * discussion of constant modules in the ExprNode interface.
     * <p>
     * A module is a constant module iff the following conditions are
     * satisfied:
     * <p>
     * 1. It contains no VARIABLE declarations (or other nonCONSTANT
     * declarations in an ASSUME).
     * <p>
     * 2. It contains no nonconstant operators such as prime ('),
     * ENABLED, or [].
     * <p>
     * 3. It extends and instantiates only constant modules.
     * <p>
     * NOTE: Can only be called after calling levelCheck
     */
    public final boolean isConstant() {
        // if the module contains any VARIABLE declarations, it is not a
        // constant module
        if (this.getVariableDecls().length > 0) return false;

        // If the module contains any non-constant operators, it is not a
        // constant module.  We test this by checking the level of the
        // bodies of the opDefs.  We enumerate this module's Context
        // object rather than using the opDefs array, because we must
        // include all operators not only defined in this module, but also
        // inherited through extention and instantiation
        this.levelCheck(1);
        /*********************************************************************
         * isConstant() can be called from other modules.  We had better be   *
         * sure that it has already been level checked before checking the    *
         * level information for the module's opDefs.                         *
         *********************************************************************/
        final OpDefNode[] opDefs = this.getOpDefs();
        for (final OpDefNode opDef : opDefs) {
            if (opDef.getKind() != ModuleInstanceKind &&
                    opDef.getBody().getLevel() != ConstantLevel)
                return false;
        }

        // If the module contains any nonconstant expressions as Theorems
        // it is nonconstant module.  (Assumptions can only be of level 0
        // anyway, so no additional test for them is necessary here.)
        for (TheoremNode theoremNode : theoremVec) {
            if (theoremNode.getLevel() != ConstantLevel) {
                return false;
            }
        }

        // Otherwise this module is a constant module
        return true;
    }

    // TODO Change to take an action/operation that is to be executed on matching
    // symbols. That way, clients don't have to iterate the result set again.
    public Collection<SymbolNode> getSymbols(final SymbolMatcher symbolMatcher) {
        final List<SymbolNode> result = new ArrayList<>(); // TreeSet to order result.

        final Enumeration<Pair> content = this.ctxt.content();
        while (content.hasMoreElements()) {
            final SymbolNode aSymbol = content.nextElement().getSymbol();
            if (symbolMatcher.matches(aSymbol)) {
                result.add(aSymbol);
            }
        }

        Collections.sort(result);
        return result;
    }

    /**
     * walkGraph, levelDataToString, and toString methods to implement
     * ExploreNode interface
     */
    @Override
    public final String levelDataToString() {
        return "LevelParams: " + getLevelParams() + "\n" +
                "LevelConstraints: " + getLevelConstraints() + "\n" +
                "ArgLevelConstraints: " + getArgLevelConstraints() + "\n" +
                "ArgLevelParams: " + getArgLevelParams() + "\n";
    }

    @Override
    public SemanticNode[] getChildren() {
        if (children != null) {
            return children;
        }
        children =
                new SemanticNode[this.opDefs.length + this.topLevel.length];
        int i;
        for (i = 0; i < this.opDefs.length; i++) {
            children[i] = this.opDefs[i];
        }
        System.arraycopy(this.topLevel, 0, children, i + 0, this.topLevel.length);
        return children;
    }

    @Override
    public final void walkGraph(final Hashtable<Integer, ExploreNode> semNodesTable, final ExplorerVisitor visitor) {
        final Integer uid = myUID;

        if (semNodesTable.get(uid) != null) return;

        semNodesTable.put(uid, this);
        visitor.preVisit(this);
        if (ctxt != null) {
            ctxt.walkGraph(semNodesTable, visitor);
        }
        for (LevelNode levelNode : topLevelVec) {
            levelNode.walkGraph(semNodesTable, visitor);
        }
        visitor.postVisit(this);
    }

    public final void print(final int indent, final int depth, final boolean b) {
        if (depth <= 0) return;

        System.out.print(
                "*ModuleNode: " + name + "  " + super.toString(depth)
                        + "  errors: " + (errors.get().getNumErrors() == 0
                        ? "none"
                        : "" + errors.get().getNumErrors()));

        final ArrayList<String> contextEntries = ctxt.getContextEntryStringArrayList(depth - 1, b);
        for (String contextEntry : contextEntries) {
            System.out.print(Strings.indent(2 + indent, contextEntry));
        }
    }

    @Override
    public final String toString(final int depth) {
        if (depth <= 0) return "";

        final StringBuilder ret =
                new StringBuilder("\n*ModuleNode: " + name + "  " + super.toString(depth) +
                        "  constant module: " + this.isConstant() +
                        "  errors: " + (errors.get().getNumErrors() == 0
                        ? "none"
                        : "" + errors.get().getNumErrors()));

        final ArrayList<String> contextEntries = ctxt.getContextEntryStringArrayList(depth - 1, false);
        if (contextEntries != null) {
            for (String contextEntry : contextEntries) {
                if (contextEntry != null) {
                    ret.append(Strings.indent(2, contextEntry));
                } else {
                    ret.append("*** null ***");
                }
            }
        }
        ret.append(Strings.indent(2,
                "\nAllExtended: " +
                        LevelNode.HashSetToString(
                                this.getExtendedModuleSet())));

        if (!instanceVec.isEmpty()) {
            ret.append(Strings.indent(2, "\nInstantiations:"));
            for (InstanceNode instanceNode : instanceVec) {
                ret.append(Strings.indent(4, instanceNode.toString(1)));
            }
        }

        if (!assumptionVec.isEmpty()) {
            ret.append(Strings.indent(2, "\nAssumptions:"));
            for (AssumeNode assumeNode : assumptionVec) {
                ret.append(Strings.indent(4, assumeNode.toString(1)));
            }
        }

        if (!theoremVec.isEmpty()) {
            ret.append(Strings.indent(2, "\nTheorems:"));
            for (TheoremNode theoremNode : theoremVec) {
                ret.append(Strings.indent(4, theoremNode.toString(1)));
            }
        }

        if (!topLevelVec.isEmpty()) {
            ret.append(Strings.indent(2, "\ntopLevelVec: "));
            for (LevelNode levelNode : topLevelVec) {
                ret.append(Strings.indent(4, levelNode.toString(1)));
            }
        }
        return ret.toString();
    }

    @Override
    protected String getNodeRef() {
        return "ModuleNodeRef";
    }

    @Override
    protected Element getSymbolElement(final Document doc, final SymbolContext context) {
        final Element ret = doc.createElement("ModuleNode");
        ret.appendChild(appendText(doc, "uniquename", getName().toString()));

        SemanticNode[] nodes;
        // constants
        //Element constants = doc.createElement("constants");
        nodes = getConstantDecls();
        for (final SemanticNode item : nodes) {
            ret.appendChild(item.export(doc, context));
        }
        //ret.appendChild(constants);

        // variables
        //Element variables = doc.createElement("variables");
        nodes = getVariableDecls();
        for (final SemanticNode value : nodes) {
            ret.appendChild(value.export(doc, context));
        }
        //ret.appendChild(variables);

        //operators
        //Element operators = doc.createElement("definitions");
        nodes = getOpDefs();
        for (final SemanticNode semanticNode : nodes) {
            ret.appendChild(semanticNode.export(doc, context)); //was with true to expand operators
        }
        //ret.appendChild(operators);

        nodes = getTopLevel();
        for (final SemanticNode node : nodes) {
            ret.appendChild(node.export(doc, context));
        }

        return ret;
    }

}

