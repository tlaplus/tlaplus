// Portions Copyright (c) 2007 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.Hashtable;

import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.utilities.Vector;

/***************************************************************************
* This class represents a non-leaf node in the tree representing a         *
* structured proof.                                                        *
***************************************************************************/

public class NonLeafProofNode extends ProofNode {

  /*************************************************************************
  * The fields.                                                            *
  *************************************************************************/
  private LevelNode[] steps = null ;
    /***********************************************************************
    * An array of nodes representing the steps of the proof.  It is read   *
    * publicly by the method getSteps().  Since any non-leaf proof must    *
    * end with a QED step, this array has non-zero length.  Here are the   *
    * possible classes of nodes in this array and the proof steps they     *
    * represent.                                                           *
    *                                                                      *
    *   DefStepNode                                                        *
    *     Represents a sequence of operator-, function-, or                *
    *     module-definition steps.  (A module definition is something      *
    *     like "Id == INSTANCE...".)  The object's getKind() method        *
    *     tells which of these it is.                                      *
    *                                                                      *
    *   UseOrHideNode                                                      *
    *     Represents a USE or HIDE step.  The object's getKind() method    *
    *     tells which it is.                                               *
    *                                                                      *
    *   InstanceNode                                                       *
    *     Represents an INSTANCE step.                                     *
    *                                                                      *
    *   TheoremNode                                                        *
    *     Represents any numerable step--that is, any step that can        *
    *     have a number.  The step is numbered iff the object's            *
    *     getDef() method returns a non-null value, in which case          *
    *     it is a ThmOrAssumpDefNode whose getName() field returns         *
    *     the step "number".  The different types of numerable             *
    *     steps are represented as follows.                                *
    *                                                                      *
    *     - An assertion or ASSUME/PROVE step is represented as an         *
    *       ordinary theorem, so the object's getTheorem() node            *
    *       returns the ExprNode or AssumeProveNode that is the            *
    *       assertion made by the step.  The object's isSuffices()         *
    *       method returns false.                                          *
    *                                                                      *
    *       As a special case, a step of the form "@ infixop expression"   *
    *       has as its theorem an OpApplNode whose first argument is an    *
    *       OpApplNode with operator $Nop and argument (a reference to)    *
    *       the right-hand-side expression of the previous step.           *
    *                                                                      *
    *     - Before 16 Feb 2009:                                            *
    *       A "SUFFICES S" step is represented the same as the             *
    *       assertion S (which may be an expression or ASSUME/PROVE)       *
    *       except that the TheoremNode's isSuffices() method returns      *
    *       true.                                                          *
    *                                                                      *
    *       As of 16 Feb 2009:                                             *
    *       A "SUFFICES S" step is represented as a TheoremNode whose      *
    *       isSuffices() method returns true and whose getTheorem()        *
    *       method returns the following:                                  *
    *         + If S is an ASSUME/PROVE, then as an AssumeProveNode        *
    *           with suffices field true.                                  *
    *         + If S is an ExprNode, then as an OpApplNode whose           *
    *           getOperator() method returns an OpDefNode of kind          *
    *           BuiltInKind representing a dummy built-in operator         *
    *           named $Suffices.                                           *
    *                                                                      *
    *    - A QED, PICK, HAVE, TAKE, CASE, or WITNESS step is               *
    *       represented by a TheoremNode whose getTheorem() method         *
    *       returns an OpApplNode whose getOperator() method returns an    *
    *       OpDefNode of kind BuiltInKind representing a dummy built-in    *
    *       operator named $Qed, $Pick, $Have, $Take, $Pfcase, or          *
    *       $Witness.  The fields of the steps are represented as the      *
    *       argument(s) and bound-identifier fields of the OpApplNode      *
    *       object.  For example, the statement                            *
    *                                                                      *
    *          PICK x \in S, y \in T : P(x, y)                             *
    *                                                                      *
    *       is represented by the same OpApplNode as the expression        *
    *                                                                      *
    *          \A x \in S, y \in T : P(x, y)                               *
    *                                                                      *
    *       except having as getOperator() value the OpDefNode for $Pick   *
    *       instead of the one for $BoundedForall.  The statement          *
    *                                                                      *
    *          WITNESS 4 \in Nat, <<3, 2>> \in Imaginary                   *
    *                                                                      *
    *       is represented by an OpApplNode whose single argument          *
    *       is the OpApplNode representing the expression.                 *
    *                                                                      *
    *          << 4 \in Nat, <<3, 2>> \in Imaginary >>                     *
    *                                                                      *
    * For each numbered step, there is a SymbolNode having the step        *
    * number as the symbol.  For a TheoremNode step, that node is a        *
    * ThmOrOpApplDefNode whose thm node points to the step.  For any       *
    * other step, it is an OpDefNode of kind NumberedProofStepKind whose   *
    * stepNode points to the step.  These SymbolNodes are used to find     *
    * references to the numbered step that appear in the proof.            *
    * Currently, the only such references that are allowed are to          *
    * TheoremNode steps and, within the DEF clause of a USE or HIDE step   *
    * or BY proof, to a DefStepNode step.                                  *
    ***********************************************************************/
  private InstanceNode[] insts ;
    /***********************************************************************
    * These are the InstanceNodes from instantiation statements in the     *
    * module-definition steps (ones arising from steps of the form "Id ==  *
    * INSTANCE ...").  They are needed for level checking those            *
    * instantiations.                                                      *
    ***********************************************************************/
    
  private Context context;
    /***********************************************************************
    * This context contains entries for every step number and definition   *
    * made in a step at the level of this proof (that is, not in           *
    * subproofs).  For a step number, the entry is a pointer to either a   *
    * ThmOrAssumpDefNode or to a NumberedProofStepKind OpDefNode.  A tool  *
    * that deals with proofs will use this to look up user references to   *
    * step numbers.                                                        *
    ***********************************************************************/

  public NonLeafProofNode(TreeNode stn, LevelNode[] stps, 
                          InstanceNode[] inst, Context ctxt) { 
     super(NonLeafProofKind, stn); 
     this.steps   = stps ;
     this.insts   = inst;
     this.context = ctxt;
   }

  public LevelNode[] getSteps()   {return steps ;} 
  public Context     getContext() {return context ;} 

  public boolean levelCheck(int iter) { 
    /***********************************************************************
    * Level check the steps and the instantiated modules coming from       *
    * module definitions.                                                  *
    ***********************************************************************/
    if (this.levelChecked >= iter) return this.levelCorrect;
    LevelNode[] ln = new LevelNode[steps.length + insts.length] ;
    System.arraycopy(steps, 0, ln, 0, steps.length) ;
    System.arraycopy(insts, 0, ln, steps.length, insts.length) ;
    return this.levelCheckSubnodes(iter, ln) ;
   }

  /*
   * The children are the steps.
   * @see tla2sany.semantic.SemanticNode#getChildren()
   */
  public SemanticNode[] getChildren() {
      if (this.steps == null || this.steps.length == 0) {
          return null;
      }
      SemanticNode[] res = new SemanticNode[this.steps.length];
      for (int i = 0; i < steps.length; i++) {
          res[i] = steps[i];
      }
      return res;
   }

  public void walkGraph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);
    if (semNodesTable.get(uid) != null) return;
    semNodesTable.put(new Integer(myUID), this);
    for (int  i = 0; i < steps.length; i++) {
      steps[i].walkGraph(semNodesTable);
      } ;
    /***********************************************************************
    * Note: there's no need to walk the defs array because all the nodes   *
    * on it are walked from the nodes under which they appear.             *
    ***********************************************************************/

    context.walkGraph(semNodesTable) ;
      /*********************************************************************
      * Walk the ThmOrOpApplDef NumberedProofStepKind nodes.               *
      *********************************************************************/
   }  

  public String toString(int depth) {
    if (depth <= 0) return "";
    String ret = "\n*ProofNode:\n"
                  + super.toString(depth)
                  + Strings.indent(2, "\nsteps:") ;
    for (int i = 0 ; i < this.steps.length; i++) {
        ret += Strings.indent(4, this.steps[i].toString(depth-1)) ;
      } ;

    /***********************************************************************
    * The following code for printing the context field copied without     *
    * understanding from ModuleNode.java.                                  *
    ***********************************************************************/
    Vector contextEntries = context.getContextEntryStringVector(depth-1,false);
    if (contextEntries != null) {
      for (int i = 0; i < contextEntries.size(); i++) {
        if (contextEntries.elementAt(i) != null) {
          ret += Strings.indent(2, (String)contextEntries.elementAt(i));
         }
        else { ret += "*** null ***"; } ;
         }
       } ; // for i
    return ret;
   }

}
