// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sun  1 March 2009 at 14:09:26 PST by lamport

package tla2sany.semantic;

import java.util.Hashtable;

import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;

/***************************************************************************
* An assume prove node represents something like                           *
*                                                                          *
*    ASSUME A, B                                                           *
*    PROVE  C                                                              *
*                                                                          *
* The method getAssumes() returns the list A, B, each of which can be      *
*   AssumeProveNode                                                        *
*   ExprNode                                                               *
*   NewSymbNode                                                            *
*                                                                          *
* The method getProve() returns C, which must be an ExprNode.              *
*                                                                          *
* Note: The level information for the Assume/Prove includes constraints    *
* for the NEW symbols declared in the ASSUME clauses.  See comments        *
* in LevelNode.java.                                                       *
****************************************************************************/

/***************************************************************************
* 16 February 2009: LL added suffices field.                               *
*   This field is set to true iff the AssumeProveNode object is generated  *
*   by a step of the form.                                                 *
*                                                                          *
*     SUFFICES ASSUME A PROVE P                                            *
***************************************************************************/

/***************************************************************************
* YET ANOTHER KLUDGE: references to subexpressions of ASSUME/PROVEs.       *
*                                                                          *
* If the assumptions of an ASSUME/PROVE contain declarations, then we      *
* want to allow references to subexpressions of an ASSUME/PROVE only       *
* within the scope of the declared symbols.  This means that a reference   *
* ref to a subexpression exp of an ASSUME/PROVE is legal iff               *
* the following predicate is true.                                         *
*                                                                          *
*    Legal(exp, ref) ==                                                    *
*      /\ exp does not lie within the scope of a declaration in            *
*         an inner (nested) ASSUME/PROVE                                   *
*                                                                          *
*      /\ \/ exp does not lie within the scope of a declaration in an      *
*            outer ASSUME/PROVE                                            *
*                                                                          *
*         \/ IF the outer ASSUME/PROVE is the body of a SUFFICES theorem   *
*              THEN ref lies outside the theorem's proof                   *
*              ELSE ref lies within  the theorem's proof                   *
*                                                                          *
* To determine if a reference is legal, we add the following fields        *
* to an AssumeProveNode object:                                            *
*                                                                          *
*   inScopeOfDecl[i] : True iff one of assume clauses 1 .. (i-1)           *
*                      is a declaration.                                   *
*                      (Hence inScopeOfDecl[0] = false.)                   *
*                                                                          *
*   inProof : This field is useful only during the construction            *
*             of the semantic node, and is true iff SANY is                *
*             currently analyzing the proof of the theorem                 *
*             containing the ASSUME/PROVE.                                 *
*                                                                          *
* Using the fact that the AssumeProve node's goal field is non-null iff    *
* the ASSUME/PROVE is an outer-level one (at least if the goal is a        *
* named theorem or proof step), this makes it easy to check if             *
* Legal(exp, ref) is true when ref is a positional subexpression.  In      *
* particular, if rho is a legal reference to an ASSUME/PROVE node ap,      *
* then                                                                     *
*                                                                          *
*   Legal(exp, rho!i) =                                                    *
*     \/ ~ ap.inScopeOfDecl[i]                                             *
*     \/ /\ ap.goal # null                                                 *
*        /\ ap.goal.suffices = ~ ap.inProof                                *
*                                                                          *
* This is implemented in Generator.illegalAPPosRef.                        *
*                                                                          *
* To handle label references, we must first ensure that the parser does    *
* not allow a label within the scope of a declaration from an inner        *
* ASSUME/PROVE. (In Generator.generateAssumeProve, this is handled using   *
* noLabelsAllowed and assumeProveDepth.)  We can then determine if         *
* Legal(exp, ref) is true for a label reference by using the label's goal  *
* and goalClause fields, and the suffices field of the goal's TheoremNode  *
* (which is copied in the goal node).  More precisely, if rho is a legal   *
* reference, then rho!lab is a legal reference iff                         *
*                                                                          *
*    LET ap == lab.goal                                                    *
*    IN  \/ ap = null                                                      *
*        \/ ~ ap.inScopeOfDecl[lab.goalClause]                             *
*        \/ /\ ap.goal # null                                              *
*           /\ ap.goal.suffices = ~ ap.inProof                             *
*                                                                          *
* The negation of this formula is computed by Generator.illegalLabelRef    *
***************************************************************************/

public class AssumeProveNode extends LevelNode {

  /*************************************************************************
  * The descendants.                                                       *
  *************************************************************************/
  protected LevelNode[] assumes = null ;
  protected ExprNode    prove   = null ;

  /*************************************************************************
  * Other fields: see their descriptions above.                            *
  *************************************************************************/
  protected boolean[] inScopeOfDecl ;
  protected boolean   inProof = true ;

  /*************************************************************************
  * suffices field added 16 Feb 2009.                                      *
  * This field is used only in Generator.selectorToNode.                   *
  *************************************************************************/
  protected boolean suffices = false ;
  protected boolean isSuffices()  {return this.suffices ;}; 
            void    setSuffices() {this.suffices = true;}; 
  public boolean getSuffices() {
      return suffices;
  }

  /**
   * The following field is set true iff this is a []ASSUME/[]PROVE node.
   * This flag is not used by SANY or any current tool, but it's
   * here just in case it will ever be used by a future tool.
   */
  protected boolean isBoxAssumeProve ;
  public boolean getIsBoxAssumeProve() {
      return isBoxAssumeProve;
  }
  protected void setIsBoxAssumeProve(boolean value) {
      isBoxAssumeProve = value;
  }

  private ThmOrAssumpDefNode goal = null ;
    /***********************************************************************
    * This is the named theorem or proof-step node whose body the          *
    * ASSUME/PROVE is.  Otherwise, it equals null.  In particular, it      *
    * equals null for an inner ASSUME/PROVE                                *
    *                                                                      *
    * This comment was wrong until LL added the code to                    *
    * Generator.generateAssumeProve to make it true on 9 Nov 2009.         *
    ***********************************************************************/
    
  /*************************************************************************
  * The Constructor.                                                       *
  *************************************************************************/
  public AssumeProveNode(TreeNode stn, ThmOrAssumpDefNode gl) {
    super(AssumeProveKind, stn);
    this.goal = gl ;
  }

  /*************************************************************************
  * The methods for finding the descendants.                               *
  *************************************************************************/
  public final SemanticNode[] getAssumes() {
    return assumes;
  }

  public final ExprNode getProve() {
    return prove;
  }

  public ThmOrAssumpDefNode getGoal() {return goal; }


  /*************************************************************************
  * Fields and methods for implementing the LevelNode interface.           *
  * The fields are all set by the levelCheck  method.                      *
  *************************************************************************/
// These fields are now part of all LevelNode subclasses.
//  private boolean levelCorrect;
//  private int level;
//  private HashSet levelParams;
//  private SetOfLevelConstraints levelConstraints;
//  private SetOfArgLevelConstraints argLevelConstraints;
//  private HashSet argLevelParams;

  /*************************************************************************
  * I implemented the levelCheck  method by copying from the method of     *
  * the same name in the OpApplNode class, using the assumptions and       *
  * prove expression the same way the ranges expressions are used to       *
  * compute the level-related fields for an OpApplNode.  This seems        *
  * reasonable, but I don't know if it's really correct.  -   LL           *
  *************************************************************************/
  public boolean levelCheck(int iter) {
    /***********************************************************************
    * Return immediately if this this.levelCheck(i) has already been       *
    * invoked for i >= iter.                                               *
    ***********************************************************************/
    if (levelChecked >= iter) return this.levelCorrect;
    levelChecked = iter ;    

    this.levelCorrect = true;

    /***********************************************************************
    * Level check assumptions.                                             *
    ***********************************************************************/
    for (int i = 0; i < this.assumes.length; i++) {
      if (this.assumes[i] != null && !this.assumes[i].levelCheck(iter)) 
       {this.levelCorrect = false;};
      }; // end for

    /***********************************************************************
    * Level check prove expression                                         *
    ***********************************************************************/
    this.prove.levelCheck(iter) ;

    /***********************************************************************
    * Calculate level.                                                     *
    ***********************************************************************/
    this.level = this.prove.getLevel() ;
    for (int i = 0; i < this.assumes.length; i++) {
      this.assumes[i].levelCheck(iter) ;
        /*******************************************************************
        * Must call levelCheck before calling getLevel.                    *
        *******************************************************************/
      if (this.assumes[i].getLevel() > level)
        { level = this.assumes[i].getLevel() ;} ;
     } ;    

    /***********************************************************************
    * Calculate levelParams and allParams.                                 *
    ***********************************************************************/
//    this.levelParams = new HashSet();
    this.levelParams.addAll(this.prove.getLevelParams());
    this.allParams.addAll(this.prove.getAllParams());
    for (int i = 0; i < this.assumes.length; i++) { 
      this.levelParams.addAll(this.assumes[i].getLevelParams()); 
      this.allParams.addAll(this.assumes[i].getAllParams()); 
     }; // for i

    /***********************************************************************
    * Calculate levelConstraints.                                          *
    ***********************************************************************/
//    this.levelConstraints = new SetOfLevelConstraints();
    this.levelConstraints.putAll(this.prove.getLevelConstraints());
    for (int i = 0; i < this.assumes.length; i++) 
      { this.levelConstraints.putAll(this.assumes[i].getLevelConstraints());
      } ;

    /***********************************************************************
    * Calculate argLevelConstraints.                                       *
    ***********************************************************************/
//    this.argLevelConstraints = new SetOfArgLevelConstraints();
    this.argLevelConstraints.putAll(this.prove.getArgLevelConstraints());
    for (int i = 0; i < this.assumes.length; i++) {
       this.argLevelConstraints.putAll(this.assumes[i].getArgLevelConstraints());
     } ;
    
    /***********************************************************************
    * Calculate argLevelParamams.                                          *
    ***********************************************************************/
//    this.argLevelParams = new HashSet();
    this.argLevelParams.addAll(this.prove.getArgLevelParams()) ;
    for (int i = 0; i < this.assumes.length; i++) {
       this.argLevelParams.addAll(this.assumes[i].getArgLevelParams());
      };
    /***********************************************************************
    * The following added on 1 Mar 2009.  See                              *
    * LevelNode.addTemporalLevelConstraintToConstants.                     *
    ***********************************************************************/
    if (this.levelCorrect) { 
      addTemporalLevelConstraintToConstants(this.levelParams,
                                            this.levelConstraints);
     };
    return this.levelCorrect ;
   } // end levelCheck


//  public int getLevel() {
//     return level ;
//   }
//
//
//  public HashSet getLevelParams() {
//     return levelParams ;
//   } 
//    /***********************************************************************
//    * Seems to return a HashSet of OpDeclNode objects.  Presumably, these  *
//    * are the parameters from the local context that contribute to the     *
//    * level of the object.                                                 *
//    ***********************************************************************/
//
//  public SetOfLevelConstraints getLevelConstraints() {
//     return levelConstraints;
//   }
//    /***********************************************************************
//    * This is a HashMap of elements whose key is a SymbolNode and whose    *
//    * value is an int.  An entry in this table means that the              *
//    * key/parameter must have a level <= the value/int.                    *
//    ***********************************************************************/
//
//  public SetOfArgLevelConstraints getArgLevelConstraints() {
//     return argLevelConstraints ;
//    }
//    /***********************************************************************
//    * An element in this HashMap has key that is a ParamAndPosition and    *
//    * value that is an int.  Such an element with key k and value v means  *
//    * that the operator parameter described by the SymbolNode k.param      *
//    * must be able to accept an argument of level v in its argument        *
//    * number k.position.                                                   *
//    ***********************************************************************/
//    
//
//  public  HashSet getArgLevelParams() {
//     return argLevelParams;
//    }
//    /***********************************************************************
//    * Seems to return a HashSet of ArgLevelParam objects.  (See            *
//    * ArgLevelParam.java for an explanation of those objects.)             *
//    ***********************************************************************/
  /*************************************************************************
  * End fields and methods implementing the LevelNode interface:           *
  *************************************************************************/

  /*************************************************************************
  * Fields and methods implementing the ExplorerNode  interface:           *
  *************************************************************************/
//  public final String levelDataToString() { 
//    return "Level: "               + this.getLevel()               + "\n" +
//           "LevelParameters: "     + this.getLevelParams()         + "\n" +
//           "LevelConstraints: "    + this.getLevelConstraints()    + "\n" +
//           "ArgLevelConstraints: " + this.getArgLevelConstraints() + "\n" +
//           "ArgLevelParams: "      + this.getArgLevelParams()      + "\n";
//  }

  
  /**
   * The children of this node are the assumes and prove expressions.
   */
  public SemanticNode[] getChildren() {
     SemanticNode[] res = new SemanticNode[this.assumes.length + 1];
     res[assumes.length] = this.prove;
     for (int i = 0; i < assumes.length; i++) {
         res[i] = assumes[i];
     }
     return res;
  }

  public final void walkGraph(Hashtable h) {
    Integer uid = new Integer(myUID);
    if (h.get(uid) != null) return;
    h.put(uid, this);
    int i = 0 ;
    while (i <  assumes.length) {
      assumes[i].walkGraph(h) ;
      i = i+1;
     } ;
    prove.walkGraph(h) ;
  } // end walkGraph()


  /*
   * Displays this node as a String, implementing ExploreNode interface; depth
   * parameter is a bound on the depth of the portion of the tree that is displayed.
   */
  public final String toString(int depth) {
    if (depth <= 0) return "";
    String assumeStr = "" ;
    int i = 0 ;
    while (i < assumes.length) {
      assumeStr = assumeStr + Strings.indent(4, assumes[i].toString(depth-1)) ;
      i = i+1;
     } ;
    String goalStr = "null" ;
    if (goal != null) {goalStr = Strings.indent(4, goal.toString(1));};
    return "\n*AssumeProveNode: " 
             + super.toString(depth)  // Seems to print stn.getLocation() where stn is the 
                                      // corresponding syntax tree node.
             + "\n  " + (isBoxAssumeProve ? "[]" : "") + "Assumes: " + assumeStr
             + "\n  " + (isBoxAssumeProve ? "[]" : "") + "Prove: " + Strings.indent(4, prove.toString(depth-1))
             + "\n  Goal: "  + goalStr 
             + ((suffices) ? "\n  SUFFICES" : "") ;
  }
  /*************************************************************************
  * End fields and methods implementing the ExplorerNode interface:        *
  *************************************************************************/
}

  

