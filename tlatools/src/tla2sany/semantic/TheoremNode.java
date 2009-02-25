// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// last modified on Tue 24 February 2009 at 16:49:51 PST by lamport

// Changed by LL on 17 Mar 2007 to handle THEOREM ASSUME ...
//   Replaced theoremExpr field with theoremExprOrAssumeProve.

/***************************************************************************
* XXXXXX To be done.  Add an isExpr() method to say whether or not the     *
* theorem is an ASSUME/PROVE                                               *
***************************************************************************/

package tla2sany.semantic;

import java.util.Hashtable;

import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import util.UniqueString;

/**
 * This class represents a theorem
 */

/***************************************************************************
* In SANY1, this class simply extended SemanticNode.  I don't know why,    *
* since level checking was performed on theorems.                          *
***************************************************************************/

public class TheoremNode extends LevelNode {

  ModuleNode  module;
  LevelNode  theoremExprOrAssumeProve;
    /***********************************************************************
    * This can be either an ExprNode or an AssumeProveNode object.         *
    ***********************************************************************/
  ThmOrAssumpDefNode   def;
    /***********************************************************************
    * For a named theorem, that is one of the form                         *
    * "THEOREM foo == ...", this is the ThmOrAssumpDefNode for the         *
    * definition.                                                          *
    ***********************************************************************/
   boolean suffices = false ;
     /**********************************************************************
     * If the node represents a proof step, then this is true iff that     *
     * step is a SUFFICES step.                                            *
     **********************************************************************/
     
   ProofNode proof;
     /**********************************************************************
     * The proof, if there is one; else null.                              *
     **********************************************************************/
//  Theorems can no longer be local.
//  boolean     localness;
  
  /** 
   * Constructor -- expr is the statement (i.e. expression or assume/prove) 
     of the theorem.
   */
  public TheoremNode(TreeNode stn, LevelNode theorem, ModuleNode mn,
                     ProofNode pf, ThmOrAssumpDefNode opd) {
    super(TheoremKind, stn);
    this.theoremExprOrAssumeProve = theorem;
    this.module = mn;
    this.def = opd;
    this.proof = pf;  // XXXXX a placeholder
  }

  /* Returns the statement of the theorem  */
  public final LevelNode getTheorem() { return this.theoremExprOrAssumeProve; }

  /*************************************************************************
  * Returns the definition, which is non-null iff this is a named          *
  * theorem.                                                               *
  *************************************************************************/
  public final ThmOrAssumpDefNode getDef() {return this.def;}
//  public final boolean isLocal() { return false; }

  /*************************************************************************
  * Return the value of the suffices field.  (See its declaration.)        *
  *************************************************************************/
  public final boolean isSuffices() {return this.suffices;}

  /*************************************************************************
  * Return the proof of the theorem, which is null if there is none.       *
  *************************************************************************/
  public final ProofNode getProof() {return this.proof;}

  /*************************************************************************
  * Return the name of the theorem if it is a named theorem, else return   *
  * null.                                                                  *
  *************************************************************************/
  public final UniqueString getName() {
    if (def == null) {return null;} ;
    return def.getName() ;
    } 

  /* Level checking */

  int levelChecked = 0 ;
  public final boolean levelCheck(int iter) {
    if (levelChecked >= iter) {return true ;} ;
    levelChecked = iter;
    LevelNode sub[] ;
    if (this.proof != null) {
      sub = new LevelNode[2];
      sub[1] = proof;
     }
    else { sub = new LevelNode[1];} ;
    if (this.def != null) {sub[0] = this.def;}
    else {sub[0] = this.theoremExprOrAssumeProve;} ;
    boolean retVal = levelCheckSubnodes(iter, sub);    
    /***********************************************************************
    * Added 24 Feb 2009: Check that                                        *
    *  - A constant theorem can have only a constant-level proof.          *
    *  - Only a temporal theorem can have a temporal-level proof.          *
    ***********************************************************************/
    if (   (this.proof != null)  
           /****************************************************************
           * Must not check if this is a QED step.                         *
           ****************************************************************/
        && ! (   (this.theoremExprOrAssumeProve != null)
              && (this.theoremExprOrAssumeProve instanceof OpApplNode)
              && (((OpApplNode) 
                     this.theoremExprOrAssumeProve).operator != null)
              && (((OpApplNode) 
                     this.theoremExprOrAssumeProve).operator.getName() 
                         == OP_qed))) {
      if (   (this.theoremExprOrAssumeProve.level == ConstantLevel)
          && (this.proof.level > ConstantLevel)) {
         errors.addError(
            stn.getLocation(),
            "Constant theorem or proof step has non-constant proof.");
          return false;
        };
      if(   (this.proof.level == TemporalLevel)
         && (this.theoremExprOrAssumeProve.level < TemporalLevel)) {
          errors.addError(
            stn.getLocation(),
            "Non-temporal theorem has temporal-level proof.");
          return false;
        };
     };
   return retVal; 
  }

//  public final int getLevel() {
//    if (levelChecked == 0) 
//      {Assert.fail("getLevel called for TheoremNode before levelCheck");};
//    return this.theoremExprOrAssumeProve.getLevel();
//  }
//
//  public final HashSet getLevelParams() {
//    if (levelChecked == 0) 
//      {Assert.fail("getLevelParams called for ThmNode before levelCheck");};
//    return this.theoremExprOrAssumeProve.getLevelParams();
//  }
//
//  public final SetOfLevelConstraints getLevelConstraints() {
//    if (levelChecked == 0) 
//     {Assert.fail("getLevelConstraints called for ThmNode before levelCheck");};
//    return this.theoremExprOrAssumeProve.getLevelConstraints();
//  }
//
//  public final SetOfArgLevelConstraints getArgLevelConstraints() {
//    if (levelChecked == 0) 
//      {Assert.fail(
//        "getArgLevelConstraints called for ThmNode before levelCheck");};
//    return this.theoremExprOrAssumeProve.getArgLevelConstraints();
//  }
//
//  public final HashSet getArgLevelParams() {
//    if (levelChecked == 0) 
//      {Assert.fail("getArgLevelParams called for ThmNode before levelCheck");};
//    return this.theoremExprOrAssumeProve.getArgLevelParams();
//  }
  
  /**
   * toString, levelDataToString, and walkGraph methods to implement
   * ExploreNode interface
   */
  public final String levelDataToString() { 
    return "Level: "               + this.getLevel()               + "\n" +
           "LevelParameters: "     + this.getLevelParams()         + "\n" +
           "LevelConstraints: "    + this.getLevelConstraints()    + "\n" +
           "ArgLevelConstraints: " + this.getArgLevelConstraints() + "\n" +
           "ArgLevelParams: "      + this.getArgLevelParams()      + "\n";
  }

  public final String toString(int depth) {
    if (depth <= 0) return "";
    String res = 
             "\n*TheoremNode " + super.toString( depth ) +
            ((theoremExprOrAssumeProve != null)  ?
              Strings.indent(2, theoremExprOrAssumeProve.toString(depth-1))
               : "");
    if (def != null) {
      res = res + Strings.indent(
                      2, 
                      "\n def: " +
                      Strings.indent(2, this.def.toString(depth-1)));
     } ;
    if (suffices) {
      res = res + Strings.indent(
                      2, 
                      "\n SUFFICES step");
     } ;
    if (proof != null) {
      res = res + Strings.indent(
                      2, 
                      "\n proof: " +
                      Strings.indent(2, this.proof.toString(depth-1)));
     } ;
    return res ;
  }

  public final void walkGraph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);
    if (semNodesTable.get(uid) != null) return;
    semNodesTable.put(uid, this);
    if (theoremExprOrAssumeProve != null) 
      {theoremExprOrAssumeProve.walkGraph(semNodesTable);} ;
    if (proof != null) {proof.walkGraph(semNodesTable);} ;
  }

}

