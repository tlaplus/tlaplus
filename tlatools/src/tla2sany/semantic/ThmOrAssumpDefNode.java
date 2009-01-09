// Copyright (c) 2007 Microsoft Corporation.  All rights reserved.

// last modified on Fri 30 Nov 2007 at 15:58:03 PST by lamport
/***************************************************************************
* The ThmOrAssumpDefNode constructor is invoked in                         *
* semantic/Generator.java to construct the nodes corresponding to the      *
* definition in something like                                             *
*                                                                          *
*   THEOREM Foo == ...                                                     *
*                                                                          *
* The following are the only public methods that a tool is likely to       *
* call.  (Search for the method to find an explanation of what it does.)   *
*                                                                          *
*    LevelNode getBody()                                                   *
*    ModuleNode getOriginallyDefinedInModuleNode()                         *
*    boolean  isTheorem()                                                  *
*    boolean isSuffices()                                                  *
*    ProofNode getProof()                                                  *
*    FormalParamNode[] getParams()                                         *
*    ModuleNode getInstantiatedFrom()                                      *
***************************************************************************/

package tla2sany.semantic;

import java.util.Enumeration;
import java.util.Hashtable;

import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.utilities.Vector;
import util.UniqueString;

/***************************************************************************
* This node represents the definition of Foo in                            *
*                                                                          *
*    THEOREM Foo == ...                                                    *
*    ASSUME  Foo == ...                                                    *
***************************************************************************/

public class ThmOrAssumpDefNode extends SymbolNode  
         implements OpDefOrLabelNode {

  private LevelNode body        = null;   
  private ModuleNode originallyDefinedInModule = null;
  private boolean theorem       = true;
    /***********************************************************************
    * True if a theorem, false if an assumption.                           *
    ***********************************************************************/
  private boolean suffices = false ;
    /***********************************************************************
    * If this represents a theorem, then this is the value of the          *
    * TheoremNode's suffices field (which is false unless the TheoremNode  *
    * represents a SUFFICES proof step).  This is a kludge added for the   *
    * following reason.  To check if a reference ot a subexpression of an  *
    * ASSUME/PROVE is legal, we need to know whether or not the            *
    * ASSUME/PROVE lies within a SUFFICES step.  However, the reference    *
    * accesses the ThmOrAssumpDefNode, while it's the TheoremNode that     *
    * contains the suffices field.  It might seem sensible to have the     *
    * ThmOrAssumpDefNode contain a pointer to the TheoremNode.  However,   *
    * that's problematic.  For one thing, instantiation creates a new      *
    * ThmOrAssumpDefNode for the imported definition, but does not create  *
    * a new TheoremNode.  So, we copy just the suffices field (which will  *
    * be false for an instantiated node because proof steps don't get      *
    * instantiated).                                                       *
    *                                                                      *
    * This field is set by setSuffices() and read by isSuffices() ;        *
    ***********************************************************************/
    
  /*************************************************************************
  * The following field is used to implement the OpDefOrLabel interface.   *
  * It is a hashtable of OpDefNode objects representing labels within      *
  * the body that are not within the scope of an inner label or LET        *
  * definition.                                                            *
  *************************************************************************/
  private Hashtable labels = null ;    

  public int arity = 0 ;
  private FormalParamNode[] params = new FormalParamNode[0];   
    /***********************************************************************
    * A theorem or assumption definition like                              *
    *                                                                      *
    *   THEOREM foo == ...                                                 *
    *                                                                      *
    * has no parameters.  However, it can acquire parameters when          *
    * the module it's in is instantiated.                                  *
    ***********************************************************************/
   ProofNode proof;
     /**********************************************************************
     * The proof, if there is one; else null.  Obviously, only a theorem   *
     * can have a proof.                                                   *
     **********************************************************************/

  private ModuleNode instantiatedFrom = null ;
    /***********************************************************************
    * If the theorem or assumption was obtained by instantiation, then     *
    * this is the module from which it was instantiated.                   *
    ***********************************************************************/
    
  /*************************************************************************
  * The Constructor.                                                      *
  *************************************************************************/
  public ThmOrAssumpDefNode(
           UniqueString name,       // The thm/assump name.
           boolean      thm,        // true if a theorem, false if an assump.
           LevelNode    exp,        // The body
           ModuleNode   oModNode,   // Name of module.
           SymbolTable  st,         // The current value of 
                                    // Generator.symbolTable
           TreeNode stn,            // The syntax node.
           FormalParamNode[] parms, // The parameters, or null if none.
           ModuleNode   iFrom       // The instantiatedFrom field.
                           ) {
    super(ThmOrAssumpDefKind, stn, name) ;
    this.theorem    = thm;
    this.body       = exp;
    this.originallyDefinedInModule = oModNode;
      /*********************************************************************
      * Note that when this theorem or assumption is instantiated with a   *
      * parameter substitution, then the newly created ThmOrAssumpDefNode  *
      * has this field set to the instantiating module.  Thus, this field  *
      * is not useful to track down the module of origin of a theorem.     *
      *********************************************************************/
      
    if (st != null) {st.addSymbol(name, this);} ;
      /*********************************************************************
      * By some magic, this eventually puts the name into the current      *
      * module's context.                                                  *
      *********************************************************************/
    if (parms != null) {
      this.params = parms;
      this.arity = parms.length;
     } ;
    this.instantiatedFrom = iFrom ;
  }   

  /*************************************************************************
  * A place-holder constructor and a method for setting the remaining      *
  * fields.  It is used in Generator.processTheorem, where the object      *
  * needs to be created before its body is generated.  This method is      *
  * not used when created a ThmOrAssumpDefNode by instantiation, so        *
  * getInstantitedFrom will be null for this object.                       *
  *************************************************************************/
  public ThmOrAssumpDefNode(UniqueString name, TreeNode stn) {
    super(ThmOrAssumpDefKind, stn, name) ;    
   }
  
  public void construct(
           boolean      thm,       // true if a theorem, false if an assump.
           LevelNode    exp,       // The body
           ModuleNode   oModNode,  // Name of module.
           SymbolTable  st,        // The current value of 
                                   // Generator.symbolTable
           FormalParamNode[] parms // The parameters, or null if none.
                           ) {
    this.theorem    = thm;
    this.body       = exp;
    this.originallyDefinedInModule = oModNode;
    if (st != null) {st.addSymbol(name, this);} ;
      /*********************************************************************
      * By some magic, this eventually puts the name into the current      *
      * module's context.                                                  *
      *********************************************************************/
    if (parms != null) {
      this.params = parms;
      this.arity = parms.length;
     } ;
  }  

  /*************************************************************************
  * The methods.                                                           *
  *************************************************************************/
  public LevelNode getBody() {return this.body; } ;
    /***********************************************************************
    * Note: this is a LevelNode rather than an ExprNode because it could   *
    * be either an ExprNode, AssumeProve node, or an APSubstInNode whose   *
    * body is either an ExprNode or an AssumeProve node.  To check if a    *
    * node N is an ExprNode, use the test                                  *
    *                                                                      *
    *    N instanceof ExprNode                                             *
    ***********************************************************************/
    
  public ModuleNode getOriginallyDefinedInModuleNode()
    /***********************************************************************
    * This is the module for which the node was created, which for a       *
    * theorem or assumption instantiated with substitution is not the      *
    * module from which the theorem or assumption came.                    *
    ***********************************************************************/
    { return originallyDefinedInModule; } 
 
  public ModuleNode getInstantiatedFrom() { return this.instantiatedFrom ; }
    /***********************************************************************
    * If the theorem or assumption was obtained by instantiation, then     *
    * this is the module from which it was instantiated.  Otherwise, it    *
    * is null.                                                             *
    ***********************************************************************/
 
  public boolean  isTheorem()  {return this.theorem ;}
  public boolean isSuffices()  {return this.suffices ;}; 
         void    setSuffices() {this.suffices = true;}; 

  /*************************************************************************
  * Return the proof of the theorem, which is null unless this is a        *
  * theorem and it has a proof.                                            *
  *************************************************************************/
  public final ProofNode getProof() {return this.proof;}

  public final FormalParamNode[] getParams() { return this.params; }

  public final boolean isExpr() { return this.body instanceof ExprNode; }
    /***********************************************************************
    * Returns true iff the body is an ExprNode (rather than an             *
    * AssumeProveNode or APSubstInNode).                                   *
    ***********************************************************************/
    
  /*************************************************************************
  * Implementations of the abstract methods of the SymbolNode superclass.  *
  *************************************************************************/
  public final int getArity() { return this.arity;}
    /***********************************************************************
    * The name of a theorem or assumption has no parameters.               *
    ***********************************************************************/
    
  public final boolean isLocal() { return false; }
    /***********************************************************************
    * Theorem and assumption definitions are never local.                  *
    ***********************************************************************/

//  public final ModuleNode getModuleNode() { return this.moduleNode; }

  public final boolean match( OpApplNode test, ModuleNode mn ) {
    /***********************************************************************
    * True iff the current object has the same arity as the node operator  *
    * of the OpApplNode test.                                              *
    ***********************************************************************/
    SymbolNode odn = test.getOperator();
    return odn.getArity() == 0;
  } 


  /*************************************************************************
  * The following methods implement the OpDefOrLabel interface.            *
  *                                                                        *
  * These are the same as the other classes that implement the interface.  *
  * There doesn't seem to be any easy way to write these methods only      *
  * once.                                                                  *
  *************************************************************************/
  public void setLabels(Hashtable ht) {labels = ht; }
    /***********************************************************************
    * Sets the set of labels.                                              *
    ***********************************************************************/
    
  public LabelNode getLabel(UniqueString us) {
    /***********************************************************************
    * If the hashtable `labels' contains a LabelNode with name `us',       *
    * then that LabelNode is returned; otherwise null is returned.         *
    ***********************************************************************/
    if (labels == null) {return null;} ;
    return (LabelNode) labels.get(us) ;    
   }

  public boolean addLabel(LabelNode odn) {
    /***********************************************************************
    * If the hashtable `labels' contains no OpDefNode with the same name   *
    * as odn, then odn is added to the set and true is return; else the    *
    * set is unchanged and false is returned.                              *
    ***********************************************************************/
    if (labels == null) {labels = new Hashtable(); } ;
    if (labels.containsKey(odn)) {return false ;} ;
    labels.put(odn.getName(), odn) ;
    return true;
   }
  
  public LabelNode[] getLabels() {
    /***********************************************************************
    * Returns an array containing the Label objects in the hashtable       *
    * `labels'.                                                            *
    ***********************************************************************/
    if (labels == null) {return new LabelNode[0];} ;
    Vector v = new Vector() ;
    Enumeration e = labels.elements() ;
    while (e.hasMoreElements()) { v.addElement(e.nextElement()); } ;
    LabelNode[] retVal = new LabelNode[v.size()] ;
    for (int i = 0 ; i < v.size() ; i++) 
      {retVal[i] = (LabelNode) v.elementAt(i); } ;
    return retVal ;
   }

  /*************************************************************************
  * Level checking.                                                        *
  *************************************************************************/
  public boolean levelCheck(int iter) {
    if (levelChecked >= iter) {return levelCorrect;} ;
    levelChecked = iter ;
    levelCorrect        = this.body.levelCheck(iter) ;
    level               = this.body.level ;
    levelParams         = this.body.levelParams ;
    allParams           = this.body.allParams ;
    levelConstraints    = this.body.levelConstraints ;
    argLevelConstraints = this.body.argLevelConstraints ;
    argLevelParams      = this.body.argLevelParams ;
    return levelCorrect ;
   }
  
//  /*************************************************************************
//  * The implementation of the LevelNode abstract methods.  They simply     *
//  * return the corresponding values for the body.                          *
//  *************************************************************************/
//  public final LevelNode getBody()  {return this.body;}
//  public boolean levelCheck()       {return this.body.levelCheck();}
//  public int getLevel()             {return this.body.getLevel();}
//  public HashSet getLevelParams()   {return this.body.getLevelParams();}
//  public SetOfLevelConstraints getLevelConstraints() 
//    {return this.body.getLevelConstraints() ;}
//  public SetOfArgLevelConstraints getArgLevelConstraints() 
//    {return this.body.getArgLevelConstraints() ; }
//  public HashSet getArgLevelParams() 
//    {return this.body.getArgLevelParams() ; }

  /** 
   * toString, levelDataToString and walkGraph methods to implement
   * ExploreNode interface
   */
//  public final String levelDataToString() {
//    return this.body.levelDataToString();
//   }

  public final void walkGraph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);
    if (semNodesTable.get(uid) != null) return;
    semNodesTable.put(new Integer(myUID), this);
    if(this.body != null) {this.body.walkGraph(semNodesTable) ;} ;
   }

  public final String toString(int depth) {
    if (depth <= 0) return "";
    String ret = 
          "\n*ThmOrAssumpDefNode: " + this.getName().toString() +
            "  " + super.toString(depth) + 
            " arity: " + this.arity + 
            " module: " + (originallyDefinedInModule != null 
                             ? originallyDefinedInModule.getName().toString() 
                             : "<null>" ) ;
    if (instantiatedFrom != null) {ret += " instantiatedFrom: " + 
                                          instantiatedFrom.getName() ; } ;
    if (params != null) {
      String tempString = "\nFormal params: " + params.length;
      for (int i = 0; i < params.length; i++) {
        tempString += Strings.indent(2, ((params[i] != null)
                                        ? params[i].toString(depth-1) 
                                         : "\nnull"));
        } ;
      ret += Strings.indent(2,tempString);
     } ;
    if (body != null) {
        ret += Strings.indent(2, 
                             "\nisTheorem(): " + theorem +
                             "\nBody:" + 
                              Strings.indent(2, this.body.toString(depth-1)));
      } // if
    /***********************************************************************
    * The following is the same for all classes that implement the         *
    * OpDefOrLabelNode interface.                                          *
    ***********************************************************************/
    if (labels != null) {
       ret += "\n  Labels: " ;
       Enumeration list = labels.keys() ;
       while (list.hasMoreElements()) {
          ret += ((UniqueString) list.nextElement()).toString() + "  " ;
         } ;
      }  
    else {ret += "\n  Labels: null";};

    return ret ;
   }
}
