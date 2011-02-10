// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// last modified on Thu  2 July 2009 at 15:44:27 PST by lamport

// Changed by LL on 17 Mar 2007 to handle THEOREM ASSUME ...
//   Replaced theoremExpr field with theoremExprOrAssumeProve.

/***************************************************************************
* Decided not to add an isExpr() method to say whether or not the theorem  *
* is an ASSUME/PROVE                                                       *
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
    this.proof = pf;  
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
  /* (non-Javadoc)
 * @see tla2sany.semantic.LevelNode#levelCheck(int)
 */
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

    if  (this.theoremExprOrAssumeProve == null) { return retVal; } ;
      /*********************************************************************
      * I don't know if the theoremExprOrAssumeProve node can be null,     *
      * but if it is, there's no more level checking to do.                *
      *********************************************************************/
    /***********************************************************************
    * If the assertion of this theorem node is an OpApplNode,              *
    * then set oan to the node and oanOp to it's operator.                 *
    ***********************************************************************/
    OpApplNode oan = null ;
    SymbolNode oanOp = null ;
    if (this.theoremExprOrAssumeProve instanceof OpApplNode) {
       oan   = (OpApplNode) this.theoremExprOrAssumeProve ;
       oanOp = oan.operator ;
    } ;

    /***********************************************************************
    * Check that only a non-temporal theorem cannot have a temporal-level  *
    * formula in its proof.                                                *
    * Modified 3 Mar 2009:                                                 *
    *                                                                      *
    * This code was commented out by LL on 10 Feb 2011.  I decided to      *
    * eliminate all checks for a temporal formula appearing inside the     *
    * proof of a non-temporal formula.  In discussions of temporal proofs  *
    * during 2010-2011, it was deemed necessary to allow a temporal fact   *
    * (like []I) to appear in the leaf proof of a non-temporal formula     *
    * (like I).  However, it was not resolved whether or not to allow a    *
    * temporal step to appear in the proof of a non-temporal step.  We     *
    * (a) couldn't think of why this should be allowed and (b) didn't      *
    * think that outlawing it in the parser would be terribly helpful.     *
    * So, for simplicity in the implementation, I decided to permit it.    *
    * If we want to outlaw it, we need to both uncomment the following     *
    * code and also make some additional changes so the level of a         *
    * temporal fact does not influence the level of a step having that     *
    * fact as its proof.  The easiest such change is probably to change    *
    * the levelCheck method of the LeafProofNode so it set's that node's   *
    * level to zero.                                                       *
    ***********************************************************************/
//    if (   (this.proof != null)  
//           /****************************************************************
//           * Must not check if this is a QED or CASE.                      *
//           ****************************************************************/
//        && ! (   (oanOp != null)
//              && (   (oanOp.getName() == OP_qed)
//                  || (oanOp.getName() == OP_pfcase)))) {
//      if(   (this.proof.level == TemporalLevel)
//         && (this.theoremExprOrAssumeProve.level < TemporalLevel)) {
//          errors.addError(
//            stn.getLocation(),
//            "Non-temporal theorem has temporal-level proof.");
//          return false;
//        };
//     };

   /************************************************************************
   * The following code checks that a PICK step whose body is a            *
   * temporal formula can have only constant bounds--for example,          *
   * in                                                                    *
   *                                                                       *
   *   PICK c \in S : <>(x=c),                                             *
   *                                                                       *
   * the expression S must have constant level.                            *
   * Added 3 Mar 2009.                                                     *
   ************************************************************************/
   if (   (oanOp != null)
       && (oanOp.getName() == OP_pick)
       && (oan.ranges != null)
       && (this.theoremExprOrAssumeProve.level == TemporalLevel)) {
     for (int i = 0; i < oan.ranges.length; i++) {
       if (oan.ranges[i].getLevel() != ConstantLevel) {
         errors.addError(
                   oan.ranges[i].stn.getLocation(),
                   "Non-constant bound of temporal PICK.");
       }
     }
   };
   /************************************************************************
   * Finish the level checking for a temporal-level node.                  *
   * Added 3 Mar 2009.                                                     *
   ************************************************************************/
   if (this.theoremExprOrAssumeProve.level == TemporalLevel){
       LevelCheckTemporal(this.proof);  
   };
   return retVal; 
  }

  /*************************************************************************
  * The following method checks that in a proof whose current goal is a    *
  * temporal-level assertion:                                              *
  *                                                                        *
  *  - Any HAVE P or CASE P step must have P of constant-level             *
  *                                                                        *
  *  - Any TAKE or WITNESS step must have constant-level                   *
  *    bounds--e.g., in TAKE x \in S, expression S must have constant      *
  *    level.                                                              *
  *                                                                        *
  * For a CASE step (which is the only one of these steps that has a       *
  * proof) and the QED step, the method must be called to check proof of   *
  * the CASE statement.                                                    *
  * Added 4 Mar 2009.                                                      *
  *************************************************************************/
  private final static void LevelCheckTemporal(ProofNode pn) {
     /**********************************************************************
     * Return if this is not a NonLeafProof.                               *
     **********************************************************************/
     if ((pn == null) || (pn.getKind() != NonLeafProofKind)){
        return;
      };
     NonLeafProofNode pnode = (NonLeafProofNode) pn ;
     for (int i = 0; i < pnode.getSteps().length; i++) {
       /********************************************************************
       * Process the i-th proof step.                                      *
       *                                                                   *
       * If this step is a TheoremNode whose theorem is an OpApplNode      *
       * then set tnode and oanode to those nodes, otherwise set them to   *
       * null.                                                             *
       ********************************************************************/
       LevelNode node = pnode.getSteps()[i]; 
       OpApplNode  oanode = null; 
       TheoremNode tnode = null; 
       if (node.getKind() == TheoremKind) {
          tnode = (TheoremNode) node;
          if (tnode.theoremExprOrAssumeProve instanceof OpApplNode) {
            oanode = (OpApplNode) tnode.theoremExprOrAssumeProve;
          }
       };
       if (oanode != null) {
         UniqueString name = oanode.operator.getName();

         if (   (   (name == OP_take) 
                 || (name == OP_witness)
                 || (name == OP_have) ) 
             && (oanode.getLevel() != ConstantLevel)) {
                   errors.addError(
                     oanode.stn.getLocation(),
                     "Non-constant TAKE, WITNESS, or HAVE " +
                     "for temporal goal.");
         } else 
         if (name == OP_pfcase) {
           /****************************************************************
           * This is a CASE, check that its argument is constant and then  *
           * recursively call LevelCheckTemporal on its proof.             *
           ****************************************************************/
           if (oanode.getLevel() != ConstantLevel){
               errors.addError(
                 oanode.stn.getLocation(),
                 "Non-constant CASE for temporal goal.") ; 
             };
           LevelCheckTemporal(tnode.getProof()) ;
         } else 
         if (name == OP_qed) {
           LevelCheckTemporal(tnode.getProof()) ;  
         }
       }; // if (oanode != null)

     } // for i
  } // LevelCheckTemporal

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

  /**
   * The children are the statement and the proof (if there is one).
   */
  
  public SemanticNode[] getChildren() {
    if (this.proof == null) {
    return new SemanticNode[] {this.theoremExprOrAssumeProve};
    }
    return new SemanticNode[] {this.theoremExprOrAssumeProve, 
                               this.proof};
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

