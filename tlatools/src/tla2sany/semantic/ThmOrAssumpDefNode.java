// Copyright (c) 2007 Microsoft Corporation.  All rights reserved.

// last modified on Thu  2 July 2009 at 15:44:33 PST by lamport
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
import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;

import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.utilities.Vector;
import util.UniqueString;
import util.WrongInvocationException;

/***************************************************************************
* This node represents the definition of Foo in                            *
*                                                                          *
*    THEOREM Foo == ...                                                    *
*    ASSUME  Foo == ...                                                    *
***************************************************************************/

public class ThmOrAssumpDefNode extends SymbolNode  
         implements OpDefOrLabelNode, AnyDefNode {

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
    * following reason.  To check if a reference to a subexpression of an  *
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
  public Hashtable  getLabelsHT() {
      /***********************************************************************
      * Return the labels field.  Used to "clone" an OpDefNode for module    *
      * instantiation.                                                       *
      ***********************************************************************/
      return labels ;
     }

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
  
  /**
   *  The source field and its methods was added by LL on 15 June 2010.
   *  I don't know why it wasn't added to this class when it was added
   *  to OpDefNode.  However, it's needed by the Toolbox, so it's being
   *  added now by trying to duplicate what was done for OpDefNode
   */
  private ThmOrAssumpDefNode source = null;
  
  public ThmOrAssumpDefNode getSource() {
      if (source == null) {
          return this;
      }
      return source;
  }
  
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
           ModuleNode   iFrom,      // The instantiatedFrom field.
           ThmOrAssumpDefNode src   // The source field.
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
    // On 1 Nov 2012,, LL moved the following two statements to here from
    // the end of the constructor.  It's necessary for the source field to be 
    // set before addSymbol is called.
    this.instantiatedFrom = iFrom ;
    this.source = src;
 
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

  // Modified by LL on 30 Oct 2012 to handle locally instantiated theorems
  // and assumptions.
  private boolean local = false ;
  public final boolean isLocal() { return local; }
    /***********************************************************************
    * Theorem and assumption definitions are local iff imported with a     *
    * LOCAL instance.                                                      *
    ***********************************************************************/
  public final void setLocal(boolean localness) {
      local = localness ;
  }
  
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

// On 24 Oct 2012 replaced the following levelCheck method with the current
// one, which was obtained by cloning the method from OpDefNode with some
// simplifications that were possible because a theorem or assumption, unlike
// and ordinary definition, cannot appear in the scope of a RECURSIVE declaration.
// He also made the ThmOrAssumpDefNode implement the AnyNode interface.
// See the comments in AnyDefNode.java for an explanation of why.

//  /*************************************************************************
//  * Level checking.                                                        *
//  *************************************************************************/
//  public boolean levelCheck(int iter) {
//    if (levelChecked >= iter) {return levelCorrect;} ;
//    levelChecked = iter ;
//    levelCorrect        = this.body.levelCheck(iter) ;
//    level               = this.body.level ;
//    levelParams         = this.body.levelParams ;
//    allParams           = this.body.allParams ;
//    levelConstraints    = this.body.levelConstraints ;
//    argLevelConstraints = this.body.argLevelConstraints ;
//    argLevelParams      = this.body.argLevelParams ;
//    return levelCorrect ;
//   }
//  
////  /*************************************************************************
////  * The implementation of the LevelNode abstract methods.  They simply     *
////  * return the corresponding values for the body.                          *
////  *************************************************************************/
////  public final LevelNode getBody()  {return this.body;}
////  public boolean levelCheck()       {return this.body.levelCheck();}
////  public int getLevel()             {return this.body.getLevel();}
////  public HashSet getLevelParams()   {return this.body.getLevelParams();}
////  public SetOfLevelConstraints getLevelConstraints() 
////    {return this.body.getLevelConstraints() ;}
////  public SetOfArgLevelConstraints getArgLevelConstraints() 
////    {return this.body.getArgLevelConstraints() ; }
////  public HashSet getArgLevelParams() 
////    {return this.body.getArgLevelParams() ; }

  /*************************************************************************
  * The fields used for level checking.                                    *
  *************************************************************************/
// These fields are now present in all LevelNode subclasses
//  private boolean levelCorrect;
//  private int level;
//  private HashSet levelParams;
//  private SetOfLevelConstraints levelConstraints;
//  private SetOfArgLevelConstraints argLevelConstraints;
//  private HashSet argLevelParams;


  int[] maxLevels;
  int[] weights;
  int[][] minMaxLevel;
    /***********************************************************************
    * According to LevelSpec.tla, if this is the OpDefNode for the         *
    * definition of op, then op.minMaxLevel[i][k] is the minimum value of  *
    * oparg.maxLevels[k] for the i-th argument of Op.  Thus,               *
    * op.minMaxLevels[i] is a sequence whose length is the number of       *
    * arguments taken by the i-th argument of Op.  (It equals 0 if the     *
    * i-th argument of Op is not an operator argument.)                    *
    ***********************************************************************/

  boolean[] isLeibnizArg;
  boolean   isLeibniz;
    /***********************************************************************
    * If this is the OpDefNode for the definition of op, then              *
    * isLeibnizArg[i] is true iff the i-th argument of op is Leibniz, and  *
    * isLeibniz = \A i : isLeibnizArg[i]                                   *
    ***********************************************************************/
  public boolean[] getIsLeibnizArg() {
      return isLeibnizArg; 
  }
  public boolean getIsLeibniz() {
      return isLeibniz; 
  }
  private boolean[][][] opLevelCond;
    /***********************************************************************
    * According to LevelSpec.tla, if thisnode defines op,                  *
    * then op.opLevelCond[i][j][k] is true iff                             *
    * the i-th argument of op is an operator argument opArg, and the       *
    * definition of op contains an expression in which the j-th formal     *
    * parameter of the definition of op appears within the k-th argument   *
    * of opArg.                                                            *
    ***********************************************************************/
  public final boolean levelCheck(int itr) {
      if (this.levelChecked >= itr) { return this.levelCorrect; }
      this.levelChecked = itr ;
      
      /***********************************************************************
      * Initialize maxLevels to the least restrictive value and weights to 0.*
      * Initialize isLeibniz and all isLeibniz[i] to true.                   *
      ***********************************************************************/
      this.maxLevels    = new int[this.params.length];
      this.weights      = new int[this.params.length];
      for (int i = 0 ; i < this.params.length ; i++) {
          this.maxLevels[i] = MaxLevel ;
          this.weights[i] = 0 ;
          this.isLeibniz    = true;
          this.isLeibnizArg = new boolean[this.params.length];
          this.isLeibnizArg[i] = true ;
        } ;


   // Level check the body:
      this.levelCorrect = this.body.levelCheck(itr);
      this.level = this.body.getLevel();
      
      SetOfLevelConstraints lcSet = this.body.getLevelConstraints();
      for (int i = 0; i < this.params.length; i++) {
         Object plevel = lcSet.get(params[i]);
         if (plevel != null) {
             this.maxLevels[i] = ((Integer)plevel).intValue();
           }
      }
      
      for (int i = 0; i < this.params.length; i++) {
          if (this.body.getLevelParams().contains(this.params[i])) {
            this.weights[i] = this.weights[i];
          }
        }
      
      this.minMaxLevel = new int[this.params.length][];
      SetOfArgLevelConstraints alcSet = this.body.getArgLevelConstraints();
      for (int i = 0; i < this.params.length; i++) {
        int alen = this.params[i].getArity();
        this.minMaxLevel[i] = new int[alen];
        for (int j = 0; j < alen; j++) {
          Object alevel = alcSet.get(new ParamAndPosition(this.params[i], j));
          if (alevel == null) {
            this.minMaxLevel[i][j] = MinLevel;
          }
          else {
            this.minMaxLevel[i][j] = ((Integer)alevel).intValue();
          }
        }
      }
      
      this.opLevelCond = new boolean[this.params.length][this.params.length][];
      HashSet alpSet = this.body.getArgLevelParams();
      for (int i = 0; i < this.params.length; i++) {
        for (int j = 0; j < this.params.length; j++) {
          this.opLevelCond[i][j] = new boolean[this.params[i].getArity()];
          for (int k = 0; k < this.params[i].getArity(); k++) {
            ArgLevelParam alp = new ArgLevelParam(this.params[i], k, this.params[j]);
            this.opLevelCond[i][j][k] = alpSet.contains(alp);
          }
        }
      }
      
      this.levelParams.addAll(this.body.getLevelParams());
      this.allParams.addAll(this.body.getAllParams());
      this.nonLeibnizParams.addAll(this.body.getNonLeibnizParams());
      for (int i = 0; i < this.params.length; i++) {
        this.levelParams.remove(this.params[i]);
        this.allParams.remove(this.params[i]);
        if (this.nonLeibnizParams.contains(this.params[i])) {
          /*******************************************************************
          * The i-th argument is non-Leibniz if this.params[i] is in the     *
          * body's nonLeibnizParams hashset (and hence now in this node's    *
          * nonLeibnizParams hashset.                                        *
          *******************************************************************/
          this.nonLeibnizParams.remove(this.params[i]) ;
          this.isLeibnizArg[i] = false ;
          this.isLeibniz = false ;
         } ;
      }

      this.levelConstraints = (SetOfLevelConstraints)lcSet.clone();
      for (int i = 0; i < this.params.length; i++) {
        this.levelConstraints.remove(this.params[i]);
      }

      this.argLevelConstraints = (SetOfArgLevelConstraints)alcSet.clone();
      for (int i = 0; i < this.params.length; i++) {
        int alen = this.params[i].getArity();
        for (int j = 0; j < alen; j++) {
          this.argLevelConstraints.remove(new ParamAndPosition(this.params[i], j));
        }
      }

      Iterator iter = alpSet.iterator();
      while (iter.hasNext()) {
        ArgLevelParam alp = (ArgLevelParam)iter.next();
        if (!alp.op.occur(this.params) ||
            !alp.param.occur(this.params)) {
          this.argLevelParams.add(alp);
        }
      }

      return levelCorrect ;
  }
  
  /***************************************************************************
  * The following Asserts can be removed after debugging.                    *
  ***************************************************************************/
    public final int getMaxLevel(int i) {
      if (this.levelChecked == 0) 
        {throw new WrongInvocationException("getMaxLevel called before levelCheck");};
      int idx = (this.getArity() == -1) ? 0 : i;
      return this.maxLevels[idx];
    }

    public final int getWeight(int i) {
      if (this.levelChecked == 0) 
        {throw new WrongInvocationException("getWeight called before levelCheck");};
      int idx = (this.getArity() == -1) ? 0 : i;
      return this.weights[idx];
    }  

    public final int getMinMaxLevel(int i, int j) {
      if (this.levelChecked == 0) 
        {throw new WrongInvocationException("getMinMaxLevel called before levelCheck");};
      if (this.minMaxLevel == null) {
        return ConstantLevel;
      }
      return this.minMaxLevel[i][j];
    }

    public final boolean getOpLevelCond(int i, int j, int k) {
      if (this.levelChecked == 0) 
        {throw new WrongInvocationException("getOpLevelCond called before levelCheck");};
      if (this.opLevelCond == null) {
        return false;
      }
      return this.opLevelCond[i][j][k];
    }
  
  /** 
   * toString, levelDataToString and walkGraph methods to implement
   * ExploreNode interface
   */
//  public final String levelDataToString() {
//    return this.body.levelDataToString();
//   }



  /**
   *  The body is the node's only child.
   */
  public SemanticNode[] getChildren() {
    return new SemanticNode[] {this.body};
  }

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
                              Strings.indent(2, this.body.toString(depth-1)) +
                             "\nsuffices: " + this.isSuffices());
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
