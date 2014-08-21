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

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;

import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.utilities.Vector;
import util.UniqueString;
import util.WrongInvocationException;

public class ModuleNode extends SymbolNode {

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
*    Returns vector of the OpDeclNode's in the current module              *
*    representing CONSTANT declarations, including operator constants      *
*    and constants defined via EXTENDS and INSTANCE, but excluding         *
*    CONSTANTS from internal modules.                                      *
*                                                                          *
* public final OpDeclNode[] getVariableDecls() {                           *
*    Returns a vector of the OpDeclNode's in the current module            *
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
*    Appends to vector of definitions in this module; should only be       *
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
*    Appends to vector of instantiations in this module                    *
*                                                                          *
* public final ModuleNode[] getInnerModules() {                            *
*    Returns an array of all the top-level inner modules that appear in    *
*    this module.  Their submodules in turn are retrieved by again         *
*    applying this method to the ModuleNode's in the returned vector,      *
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

  private Context      ctxt;     
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

  private ModuleNode[]  extendees    = new ModuleNode[0]; 
    // Modules directly extended by this one.
    /***********************************************************************
    * This is set by createExtendeeArray, which is called by               *
    * Generator.processExtendsList.  However, its value does not seem to   *
    * be used anywhere, nor is it made available to users of the           *
    * ModuleNode class.                                                    *
    ***********************************************************************/

  private HashSet allExtendees = null ;
    /***********************************************************************
    * The set of all modules that are extended by this module--either      *
    * directly or indirectly.  Returned by getExtendModules                *
    ***********************************************************************/
    
  private OpDeclNode[] constantDecls = null; 
    // CONSTANTs declared in this module

  private OpDeclNode[] variableDecls = null; 
    // VARIABLEs declared in this module


  private Vector definitions         = new Vector(8); 
    // AssumeNodes, internal ModuleNodes, OpDefNodes, and TheoremNodes, in
    // the exact order they were defined in this module
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
    * It appears that this field is never used in SANY1.                   *
    ***********************************************************************/
    
  Vector recursiveDecls = new Vector(8);
    /***********************************************************************
    * Contains the list of OpDefNode objects created by processing         *
    * RECURSIVE statements, in the order in which they were created.       *
    ***********************************************************************/

  Vector opDefsInRecursiveSection = new Vector(16);
    /***********************************************************************
    * The list of all OpDefNode objects opd in this module, and in any     *
    * inner modules, with opd.recursiveSection >= 0.  (See the comments    *
    * for OpDefNode.recursiveSection to see what this field means.)        *
    ***********************************************************************/

  int nestingLevel ;
    /***********************************************************************
    * The number of outer modules within which this module occurs.  It     *
    * equals 0 for an outer-level module; it equals 1 for a module whose   *
    * "----- MODULE" token is at the outer level of an outer-level         *
    * module, and so on.                                                   *
    ***********************************************************************/
    
  private OpDefNode[]    opDefs         = null; 
    // operators defined in this module, in order defined
  private ThmOrAssumpDefNode[] thmOrAssDefs = null; 
    // theorems or assumptions defined in this module, in order defined
  private ModuleNode[]   modDefs        = null; 
    // inner modules defined in this module
  private InstanceNode[] instantiations = null; 
    // top level module instantiations in this module  
  private AssumeNode[]   assumptions    = null; 
    // assumptions in this module
  private TheoremNode[]  theorems       = null; 
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
  
  private boolean isStandard = false ;
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
    
  /*************************************************************************
  * The next three vectors hold the ASSUMEs, THEOREMs, and top-level       *
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
  private Vector assumptionVec = new Vector();  // Vector of AssumeNodes
  private Vector theoremVec    = new Vector();  // Vector of TheoremNodes
  private Vector instanceVec   = new Vector();  // Vector of InstanceNodes

  private Vector topLevelVec   = new Vector();
    /***********************************************************************
    * A vector containing all the entries in the preceding three vectors,  *
    * plus all top-level UseOrHideNode nodes, in the order in which they   *
    * appear in the module.                                                *
    ***********************************************************************/

  Vector recursiveOpDefNodes = new Vector();
    /***********************************************************************
    * A vector of all OpDefNodes for operators declared in RECURSIVE       *
    * statements--even within LET expressions.                             *
    ***********************************************************************/
    
  // Invoked only in Generator
  public ModuleNode(UniqueString us, Context ct, TreeNode stn) {
    super(ModuleKind, stn, us); 
    this.ctxt = ct; 
  }

  // Required for SymbolNode interface.
  public final int getArity() { return -2; }

  /**
   * This just returns null.  I don't know why its needed.
   * @return
   */
  public final SymbolTable getSymbolTable() { return null; }

  public final Context getContext() { return this.ctxt; }

  // Meaningless--just here for compatibility with SymbolNode interface
  public final boolean isLocal() { return false; }

  // Returns true iff this module has no parmeters, i.e. CONSTANT or
  // VARIABLE decls, so that INSTANCEing it is the same as EXTENDing it.
  final boolean isParameterFree() {
    return (getConstantDecls().length == 0 &&
            getVariableDecls().length == 0);
  }

  public final void createExtendeeArray(Vector extendeeVec) {
    /***********************************************************************
    * This is called by Generator.processExtendsList to set the            *
    * ModuleNode's extendees field, which never seems to be used.          *
    ***********************************************************************/
    extendees = new ModuleNode[extendeeVec.size()];

    for ( int i = 0; i < extendees.length; i++ ) {
      extendees[i] = (ModuleNode)extendeeVec.elementAt(i);
    }
  }
    
  /**
   * Returns vector of the OpDeclNode's in the current module
   * representing CONSTANT declarations, including operator constants
   * and constants defined via EXTENDS and INSTANCE, but excluding
   * CONSTANTS from internal modules.
   */
  public final OpDeclNode[] getConstantDecls() {
    if (constantDecls != null) return constantDecls;

    Vector contextVec = ctxt.getConstantDecls();
    constantDecls = new OpDeclNode[contextVec.size()];
    for (int i = 0, j = constantDecls.length - 1; i < constantDecls.length; i++) {
      constantDecls[j--] = (OpDeclNode)contextVec.elementAt(i);
    }
    return constantDecls;
  }

  /**
   * Returns a vector of the OpDeclNode's in the current module
   * representing VARIABLE declarations, including those defined via
   * EXTENDS and INSTANCE, but excluding VARIABLES from internal modules.
   */
   public final OpDeclNode[] getVariableDecls() {
    if (variableDecls != null) return variableDecls;

    Vector contextVec = ctxt.getVariableDecls();
    variableDecls = new OpDeclNode[contextVec.size()];
    for (int i = 0, j = variableDecls.length - 1; i < variableDecls.length; i++) {
      variableDecls[j--] = (OpDeclNode)contextVec.elementAt(i);
    }
    return variableDecls;
  }

  /**
   * Returns array of the OpDefNode's created in the current module,
   * including function defs, and operators those defined via EXTENDS
   * and INSTANCE, but excluding built-in operators, operators in the
   * LET-clause of a let-expression, formal parameters, bound
   * variables, and operators defined in internal modules.
   *
   * The OpDefNodes are ordered such that if B is defined in terms of
   * A, then B has a HIGHER index than A in the returned array.
   */
  public final OpDefNode[] getOpDefs() {
    if (opDefs != null) return opDefs;
    Vector contextVec = ctxt.getOpDefs();
    opDefs = new OpDefNode[contextVec.size()];
    for (int i = 0, j = opDefs.length - 1; i < opDefs.length; i++) {
        opDefs[j--] = (OpDefNode)contextVec.elementAt(i);
    }
    return opDefs;
  }

  /*************************************************************************
  * Returns an array of all ThmOrAssumpDefNode objects created in the      *
  * current module (but not in inner modules).  They should appear in the  *
  * order in which they occur in the module.  Code copied from             *
  * getOpDefs().                                                           *
  *************************************************************************/
  public final ThmOrAssumpDefNode[] getThmOrAssDefs() {
    if (thmOrAssDefs != null) return thmOrAssDefs;
    Vector contextVec = ctxt.getThmOrAssDefs();
    thmOrAssDefs = new ThmOrAssumpDefNode[contextVec.size()];
    for (int i = 0, j = thmOrAssDefs.length - 1; 
                           i < thmOrAssDefs.length; i++) {
        thmOrAssDefs[j--] = (ThmOrAssumpDefNode) contextVec.elementAt(i);
    }
    return thmOrAssDefs;
  }  

  /** 
   * Appends to vector of definitions in this module; should only be
   * called with AssumeNodes, ModuleNodes, OpDefNodes and TheoremNodes
   * as arguments.
   */
  public final void appendDef(SemanticNode s) {
    definitions.addElement(s);
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
      instantiations[i] = (InstanceNode)(instanceVec.elementAt(i));
    }
    return instantiations;
  }

  /** 
   * Appends to vector of instantiations in this module
   */
  public final void appendInstance(InstanceNode s) {
    instanceVec.addElement(s);
    topLevelVec.addElement(s);
  }

  /**
   * Returns an array of all the top-level inner modules that appear
   * in this module.  Their submodules in turn are retrieved by again
   * applying this method to the ModuleNode's in the returned vector,
   * etc.
   */
  public final ModuleNode[] getInnerModules() {
    if ( modDefs != null ) return modDefs;

    Vector v = ctxt.getModDefs();
    modDefs = new ModuleNode[v.size()];
    for (int i = 0; i < modDefs.length; i++) {
      modDefs[i] = (ModuleNode)v.elementAt(i);
    }
    return modDefs;
  }

  /**
   * Returns the array of AssumeNodes that are part of this module,
     including ones from extended (but not instantiated) modules.
   */
  public final AssumeNode[] getAssumptions() {
    if (assumptions != null) return assumptions;

    assumptions = new AssumeNode[assumptionVec.size()];
    for (int i = 0; i< assumptions.length; i++) {
      assumptions[i] = (AssumeNode)assumptionVec.elementAt(i);
    }
    return assumptions;
  }

  /**
   * Returns the array of TheoremNodes that are part of this module,
     including ones from extended (but not instantiated) modules.
   */
  public final TheoremNode[] getTheorems() {
    if (theorems != null) return theorems;

    theorems = new TheoremNode[theoremVec.size()];
    for (int i = 0; i < theorems.length; i++) {
      theorems[i] = (TheoremNode)(theoremVec.elementAt(i));
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
      topLevel[i] = (LevelNode)(topLevelVec.elementAt(i));
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
public void setInstantiated(boolean isInstantiated) {
	this.isInstantiated = isInstantiated;
}

/**
 * @return the isStandard
 */
public boolean isStandard() {
	return isStandard;
}

/**
 * @param isStandard the isStandard to set
 */
public void setStandard(boolean isStandard) {
	this.isStandard = isStandard;
}

final void addAssumption(TreeNode stn, ExprNode ass, SymbolTable st, 
                           ThmOrAssumpDefNode tadn) {
    /***********************************************************************
    * Create a new assumption node and add it to assumptionVec and         *
    * topLevelVec.                                                         *
    ***********************************************************************/
    AssumeNode an = new AssumeNode( stn, ass, this, tadn ) ;
   assumptionVec.addElement(an);
    topLevelVec.addElement(an);
  }

  final void addTheorem( TreeNode stn, LevelNode thm, ProofNode pf,
                         ThmOrAssumpDefNode tadn) {
    /***********************************************************************
    * LL Change: 17 Mar 2007 - Removed localness argument because          *
    *                          theorems cannot be local                    *
    *                        - Changed thm argument to allow               *
    *                          AssumeProveNode as well as ExprNode         *
    * LL Change: 29 Jul 2007 - Add node to topLevelVec.                    *
    ***********************************************************************/
    TheoremNode tn = new TheoremNode( stn, thm, this, pf, tadn ) ;
    theoremVec.addElement(tn);
    topLevelVec.addElement(tn);
  }

  final void addTopLevel(LevelNode nd) {
    topLevelVec.addElement(nd) ;  
   }

  final void copyAssumes(ModuleNode extendee) {
    for (int i = 0; i < extendee.assumptionVec.size(); i++) {
      AssumeNode assume = (AssumeNode)extendee.assumptionVec.elementAt(i);
      assumptionVec.addElement(assume);    
    }
  }

  final void copyTheorems(ModuleNode extendee) {
    for (int i = 0; i < extendee.theoremVec.size(); i++) {
      TheoremNode theorem = (TheoremNode)extendee.theoremVec.elementAt(i);
      theoremVec.addElement(theorem);
    }
  }

  final void copyTopLevel(ModuleNode extendee) {
    for (int i = 0; i < extendee.topLevelVec.size(); i++) {
      LevelNode node = (LevelNode)extendee.topLevelVec.elementAt(i);
      topLevelVec.addElement(node);    
    }
  }


  public final HashSet getExtendedModuleSet() {
    /***********************************************************************
    * Returns a Hashset whose elements are ModuleNode objects representing  *
    * all modules that are extended by this module--either directly or      *
    * indirectly.                                                           *
    ***********************************************************************/
    if (this.allExtendees == null) {
      this.allExtendees = new HashSet() ;
      for (int i = 0; i < this.extendees.length; i++) {
        this.allExtendees.add(this.extendees[i]) ;
        this.allExtendees.addAll(this.extendees[i].getExtendedModuleSet()) ;
       } // for
      }; //if
    return this.allExtendees ;
  }

  public boolean extendsModule(ModuleNode mod) {
    /************************************************************************
    * Returns True iff this module extends module mod--either directly or   *
    * indirectly.                                                           *
    ************************************************************************/
    return this.getExtendedModuleSet().contains(mod) ;
  } ;


  /** 
   * Just a stub method; one cannot resolve against a ModuleNode.
   * This method is here only to satisfy the SymbolNode interface.
   */
  public final boolean match( OpApplNode sn, ModuleNode mn ) { return false; } 

  /**
   * Returns an array of all the theorems that appear in this module,   
   * along with their proofs (if they have them).  It includes theorems 
   * obtained from extended and instantiated modules.  Note that if     
   * module M has ASSUME statements A and B, then                       
   *                                                                    
   *    Foo(x, y) == INSTANCE M WITH ...                                
   *                                                                    
   * introduces, for each theorem T in module M, the theorem            
   *                                                                    
   *    ASSUME 1. LEVELDECL x                                           
   *           2. LEVELDECL y                                           
   *           3. A                                                     
   *           4. B                                                     
   *    PROVE  T                                                        
   *                                                                    
   * where LEVELDECL denotes some appropriate level declaration based   
   * on the maximum levels of expressions that can be substituted       
   * for the formal parameters x and y.   
   *
   * Not implemented -- see getTheorems()                              
   */
  public final TheoremNode[] getThms() { return null; }

  /**
   * Returns an array of all the assumptions (the expressions in ASSUME 
   * statements).  An assumption in an ordinary specification has the   
   * form                                                               
   *                                                                    
   *    ASSUME A == expr                                                
   *                                                                    
   * where expr is a constant-level expression.  However, the grammar   
   * allows assumptions such as                                         
   *                                                                    
   *    ASSUME A == ASSUME B                                            
   *                PROVE  C                                            
   *                                                                    
   * Hence, an assumption must be represented by an AssumeProveNode.    
   *                                                                    
   * An assumption like this produces a ref in getAssumes() to the      
   * AssumeProveNode that represents the assumption, and a ref in       
   * getOpDefs to the OpDefNode that represents the definition of A. 
   *
   * Not implemented -- see getAssumptions()   
   */
  public final AssumeProveNode[] getAssumes() { return null; }

  /* Level checking */
//  Old level parameter fields removed and replace by subfields
//  of levelData.

//   private boolean levelCorrect;
//  private HashSet levelParams;
//  private SetOfLevelConstraints levelConstraints;
//  private SetOfArgLevelConstraints argLevelConstraints;
//  private HashSet argLevelParams;
  
  public final boolean levelCheck(int itr) {

    if (levelChecked >= itr) return this.levelCorrect;
    levelChecked = itr ;

/***************************************************************************
* REMOVE THIS CODE XXXX                                                    *
***************************************************************************/
// System.out.println("Module " + this.getName() + " has level "
//                      + this.nestingLevel);
// for (int i = 0; i < definitions.size(); i++) {
// if (definitions.elementAt(i) instanceof OpDefNode) {
// OpDefNode foo = (OpDefNode) definitions.elementAt(i) ;
// System.out.println("definitions, module " + this.getName() + ": " 
//    + foo.getName() + " rec sec: " + foo.recursiveSection) ;
// }
// else
// { System.out.println("definitions, module " + this.getName() + 
//    ": non-OpDefNode "   + ((SymbolNode) definitions.elementAt(i)).getName()) ;
// }
// };
// 
// for (int i = 0; i < opDefsInRecursiveSection.size(); i++) {
// System.out.println("opDefsInRecursiveSection, module " + this.getName() + ": " 
//    + ((SymbolNode) opDefsInRecursiveSection.elementAt(i)).getName()) ;
// };

// XXXXXXX Testing
// System.out.println("theoremVec: ") ;
// for (int i = 0 ; i < theoremVec.size(); i++) {
// System.out.println("Theorem at " + 
//     ((SemanticNode) theoremVec.elementAt(i)).stn.getLocation().toString()); 
// } ;
// 
// System.out.println("instanceVec: ") ;
// for (int i = 0 ; i < instanceVec.size(); i++) {
// System.out.println("Instance at " + 
//   ((SemanticNode) instanceVec.elementAt(i)).stn.getLocation().toString()); 
// } ;

/***************************************************************************
* Perform level checking for all operator definitions in recursive         *
* sections.  See the explanation in the file level-checking-proposal.txt,  *
* a copy of which is at the end of the file semantic/LevelNode.java.       *
***************************************************************************/
    int firstInSectIdx = 0 ;
    while (firstInSectIdx < opDefsInRecursiveSection.size()) {
      /*********************************************************************
      * Each iterate of this loop handles one recursive section whose      *
      * first OpDefNode is element firstInSectIdx of the                   *
      * opDefsInRecursiveSection vector.                                   *
      *********************************************************************/
      int curNodeIdx = firstInSectIdx ;
      OpDefNode curNode = 
          (OpDefNode) opDefsInRecursiveSection.elementAt(curNodeIdx);
      int curSection = curNode.recursiveSection ;
      boolean notDone = true ;
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
          curNode.levelChecked = 1 ;
          for (int i = 0 ; i < curNode.getArity() ; i++) {
             curNode.maxLevels[i] = ActionLevel ;
             curNode.weights[i] = 1 ;
            } // for;
          } // if (curNode.inRecursive)
         else {curNode.levelChecked = 0 ;};
        curNodeIdx++ ;
        if (curNodeIdx < opDefsInRecursiveSection.size()) {
          curNode = (OpDefNode) 
                        opDefsInRecursiveSection.elementAt(curNodeIdx);
          notDone = (curNode.recursiveSection == curSection) ;
         }
        else {notDone = false ;} ;
       }; // while (notDone)

      
      /*********************************************************************
      * Do the level checking for each operator in the recursive section,  *
      * and set maxRecursiveLevel to the maximum level and                 *
      * recursiveLevelParams to the union of the levelParams for all       *
      * recursive operators.  Do the analogous operation for allParams,    *
      * using recursiveAllParams.                                          *
      *********************************************************************/
      int maxRecursiveLevel = ConstantLevel ;
      HashSet recursiveLevelParams = new HashSet() ;
      HashSet recursiveAllParams = new HashSet() ;
      for (int i = firstInSectIdx ; i < curNodeIdx ; i++) {
        curNode = (OpDefNode) opDefsInRecursiveSection.elementAt(i) ;
        if (curNode.inRecursive) {curNode.levelChecked = 0 ;} ;
        curNode.levelCheck(1) ;

        if (curNode.inRecursive) {
          /*****************************************************************
          * For a recursive node, check for primed arguments and update    *
          * maxRecursiveLevel, recursiveLevelParams, and                   *
          * recursiveAllParams.                                            *
          *****************************************************************/
          for (int j = 0 ; j < curNode.getArity() ; j++) {
            if (curNode.maxLevels[j] < ActionLevel) {
               errors.addError(curNode.getTreeNode().getLocation(),
                             "Argument " + (j+1) + " of recursive operator "
                               + curNode.getName() + " is primed") ;
            } ; // if 
           } ; // for j 
          maxRecursiveLevel = Math.max(maxRecursiveLevel, curNode.level) ;
          recursiveLevelParams.addAll(curNode.levelParams) ;
          recursiveAllParams.addAll(curNode.allParams) ;
         }; // if (curNode.inRecursive) 
       }; // for i 

      /*********************************************************************
      * Reset the level, levelParams, allParams, and levelChecked fields   *
      * for every operator in the recursive section.                       *
      *********************************************************************/
      for (int i = firstInSectIdx ; i < curNodeIdx ; i++) {
        curNode = (OpDefNode) opDefsInRecursiveSection.elementAt(i) ;
        if (curNode.inRecursive) {curNode.levelChecked = 2;} ;
        curNode.level = Math.max(curNode.level, maxRecursiveLevel) ;
        curNode.levelParams.addAll(recursiveLevelParams) ;
        curNode.allParams.addAll(recursiveAllParams) ;
       }; // for i       

      /*********************************************************************
      * Perform the level checking again on the operators in the           *
      * recursive section.                                                 *
      *********************************************************************/
      for (int i = firstInSectIdx ; i < curNodeIdx ; i++) {
        curNode = (OpDefNode) opDefsInRecursiveSection.elementAt(i) ;
        if (curNode.inRecursive) {curNode.levelChecked = 1;} ;
        curNode.levelCheck(2) ;
       }; // for i            

      firstInSectIdx = curNodeIdx ;
     } // while (firstInSectIdx < ...) 

    /***********************************************************************
    * We now do level checking as in SANY1 for everything in the module    *
    * that wasn't just level checked.                                      *
    ***********************************************************************/
    // Level check everything in this module
    this.levelCorrect = true;
    ModuleNode[] mods = this.getInnerModules();
    for (int i = 0; i < mods.length; i++) {
      if (!mods[i].levelCheck(1)) {
        this.levelCorrect = false;
      }
    }

    OpDefNode[] opDefs = this.getOpDefs();
      /*********************************************************************
      * I don't understand why this is preceded by OpDefNode[],            *
      * presumably making it a local variable.  However, it doesn't seem   *
      * to make any difference, so I've left it.                           *
      *********************************************************************/
    for (int i = 0; i < opDefs.length; i++) {
// System.out.println("opDef, module " + this.getName() + ": "  
// + opDefs[i].getName()); 
      if (!opDefs[i].levelCheck(1)) {
        this.levelCorrect = false;
      }
    }
    thmOrAssDefs = this.getThmOrAssDefs();
    for (int i = 0; i < thmOrAssDefs.length; i++) {
// System.out.println("opDef, module " + this.getName() + ": "  
// + opDefs[i].getName()); 
      if (!thmOrAssDefs[i].levelCheck(1)) {
        this.levelCorrect = false;
      }
    }

    /***********************************************************************
    * Can use topLevel instead of the three separate arrays theorems,      *
    * assumptions, and instances.                                          *
    ***********************************************************************/
    LevelNode[] tpLev = this.getTopLevel() ;
    for (int i = 0; i < tpLev.length; i++) {
      if (!tpLev[i].levelCheck(1)) {
        this.levelCorrect = false;
      }
    } ;
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
    OpDeclNode[] decls = this.getConstantDecls();
    for (int i = 0; i < decls.length; i++) {
      this.levelParams.add(decls[i]);
      this.allParams.add(decls[i]);
    }
    
//    this.levelConstraints = new SetOfLevelConstraints();
//    this.argLevelConstraints = new SetOfArgLevelConstraints();
//    this.argLevelParams = new HashSet();
    if (!this.isConstant()) {
      for (int i = 0; i < decls.length; i++) {
        this.levelConstraints.put(decls[i], Levels[ConstantLevel]);
      }
    }
    for (int i = 0; i < opDefs.length; i++) {
      this.levelConstraints.putAll(opDefs[i].getLevelConstraints());
      this.argLevelConstraints.putAll(opDefs[i].getArgLevelConstraints());
      Iterator iter = opDefs[i].getArgLevelParams().iterator();
      while (iter.hasNext()) {
        ArgLevelParam alp = (ArgLevelParam)iter.next();
        if (!alp.occur(opDefs[i].getParams())) {
          this.argLevelParams.add(alp);
        }
      }
    }

    /***********************************************************************
    * Can use topLevel instead of the three separate arrays theorems,      *
    * assumptions, and instances.                                          *
    ***********************************************************************/
    for (int i = 0; i < tpLev.length; i++) {
      this.levelConstraints.putAll(tpLev[i].getLevelConstraints());
      this.argLevelConstraints.putAll(tpLev[i].getArgLevelConstraints());
      this.argLevelParams.addAll(tpLev[i].getArgLevelParams());      
    }

//    for (int i = 0; i < thms.length; i++) {
//      this.levelConstraints.putAll(thms[i].getLevelConstraints());
//      this.argLevelConstraints.putAll(thms[i].getArgLevelConstraints());
//      this.argLevelParams.addAll(thms[i].getArgLevelParams());      
//    }
//    for (int i = 0; i < insts.length; i++) {
//      this.levelConstraints.putAll(insts[i].getLevelConstraints());
//      this.argLevelConstraints.putAll(insts[i].getArgLevelConstraints());
//      this.argLevelParams.addAll(insts[i].getArgLevelParams());
//    }
//    for (int i = 0; i < assumps.length; i++) {
//      this.levelConstraints.putAll(assumps[i].getLevelConstraints());
//      this.argLevelConstraints.putAll(assumps[i].getArgLevelConstraints());
//      this.argLevelParams.addAll(assumps[i].getArgLevelParams());      
//    }
    return this.levelCorrect;
  }

  public final int getLevel() {
      throw new WrongInvocationException("Internal Error: Should never call ModuleNode.getLevel()");
  }
  

//  public final HashSet getLevelParams() { return this.levelParams; }
//  
//  public final SetOfLevelConstraints getLevelConstraints() { 
//    return this.levelConstraints; 
//  }
//
//  public final SetOfArgLevelConstraints getArgLevelConstraints() { 
//    return this.argLevelConstraints; 
//  }
//
//  public final HashSet getArgLevelParams() { return this.argLevelParams; }

  /**
   * Returns true iff the module is a constant module. See the
   * discussion of constant modules in the ExprNode interface.
   *
   * A module is a constant module iff the following conditions are
   * satisfied:
   *
   * 1. It contains no VARIABLE declarations (or other nonCONSTANT
   *    declarations in an ASSUME). 
   *
   * 2. It contains no nonconstant operators such as prime ('),
   *    ENABLED, or [].
   *
   * 3. It extends and instantiates only constant modules.
   *
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
    this.levelCheck(1) ;
      /*********************************************************************
      * isConstant() can be called from other modules.  We had better be   *
      * sure that it has already been level checked before checking the    *
      * level information for the module's opDefs.                         *
      *********************************************************************/
    OpDefNode[] opDefs = this.getOpDefs();
    for (int i = 0; i < opDefs.length; i++) {
      if (opDefs[i].getKind() != ModuleInstanceKind &&
          opDefs[i].getBody().getLevel() != ConstantLevel)
        return false;
    }

    // If the module contains any nonconstant expressions as Theorems
    // it is nonconstant module.  (Assumptions can only be of level 0
    // anyway, so no additional test for them is necessary here.)
    for (int i = 0; i < theoremVec.size(); i++) {
      if (((TheoremNode)(theoremVec.elementAt(i))).getLevel() != ConstantLevel) {
        return false;
      }
    }

    // Otherwise this module is a constant module
    return true;
  }

  /**  
   * walkGraph, levelDataToString, and toString methods to implement
   * ExploreNode interface
   */
  public final String levelDataToString() { 
    return "LevelParams: "         + getLevelParams()         + "\n" +
           "LevelConstraints: "    + getLevelConstraints()    + "\n" +
           "ArgLevelConstraints: " + getArgLevelConstraints() + "\n" +
           "ArgLevelParams: "      + getArgLevelParams()      + "\n";
  }

  private SemanticNode[] children = null;
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
      for (int j = 0; j < this.topLevel.length; j++) {
          children[i+j] = this.topLevel[j];
      }
      return children;
   }

  public final void walkGraph (Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);

    if (semNodesTable.get(uid) != null) return;

    semNodesTable.put(uid, this);
    if (ctxt != null) {
      ctxt.walkGraph(semNodesTable);
    }
    for (int i = 0; i < topLevelVec.size(); i++) {
      ((LevelNode)(topLevelVec.elementAt(i))).walkGraph(semNodesTable);
    }
//     for (int i = 0; i < instanceVec.size(); i++) {
//       ((InstanceNode)(instanceVec.elementAt(i))).walkGraph(semNodesTable);
//     }
//     for (int i = 0; i < theoremVec.size(); i++) {
//       ((TheoremNode)(theoremVec.elementAt(i))).walkGraph(semNodesTable);
//     }
//     for (int i = 0; i < assumptionVec.size(); i++) {
//       ((AssumeNode)(assumptionVec.elementAt(i))).walkGraph(semNodesTable);
//     }
  }

  public final void print(int indent, int depth, boolean b) {
    if (depth <= 0) return;

    System.out.print(
      "*ModuleNode: " + name + "  " + super.toString(depth) 
      + "  errors: " + (errors == null 
                           ? "null" 
                           : (errors.getNumErrors() == 0 
                                 ? "none" 
                                 : "" +errors.getNumErrors())));

    Vector contextEntries = ctxt.getContextEntryStringVector(depth-1, b);
    for (int i = 0; i < contextEntries.size(); i++) {
      System.out.print(Strings.indent(2+indent, (String)contextEntries.elementAt(i)) );
    }
  }

  public final String toString(int depth) {
    if (depth <= 0) return "";

    String ret =
      "\n*ModuleNode: " + name + "  " + super.toString(depth) + 
      "  constant module: " + this.isConstant() +
      "  errors: " + (errors == null 
                        ? "null" 
                        : (errors.getNumErrors() == 0 
                              ? "none" 
                              : "" + errors.getNumErrors()));

    Vector contextEntries = ctxt.getContextEntryStringVector(depth-1,false);
    if (contextEntries != null) {
      for (int i = 0; i < contextEntries.size(); i++) {
        if (contextEntries.elementAt(i) != null) {
          ret += Strings.indent(2, (String)contextEntries.elementAt(i));
        }
        else {
          ret += "*** null ***";
        }
      }
    }
    ret += Strings.indent(2, 
                          "\nAllExtended: " + 
                          LevelNode.HashSetToString(
                             this.getExtendedModuleSet()));

    if ( instanceVec.size() > 0 ) {
      ret += Strings.indent(2, "\nInstantiations:");
      for (int i = 0; i < instanceVec.size(); i++) {
        ret += Strings.indent(4, ((InstanceNode)(instanceVec.elementAt(i))).toString(1));
      }
    }

    if ( assumptionVec.size() > 0 ) {
      ret += Strings.indent(2, "\nAssumptions:");
      for (int i = 0; i < assumptionVec.size(); i++) {
        ret += Strings.indent(4, ((AssumeNode)(assumptionVec.elementAt(i))).toString(1));
      }
    }

    if ( theoremVec.size() > 0 ) {
      ret += Strings.indent(2, "\nTheorems:");
      for (int i = 0; i < theoremVec.size(); i++) {
        ret += Strings.indent(4, ((TheoremNode)(theoremVec.elementAt(i))).toString(1));
      }
    }

    if ( topLevelVec.size() > 0 ) {
      ret += Strings.indent(2, "\ntopLevelVec: ");
      for (int i = 0; i < topLevelVec.size(); i++) {
        ret += Strings.indent(4, ((LevelNode) topLevelVec.elementAt(i)).toString(1));
        }
      };
    return ret;
  }

}

