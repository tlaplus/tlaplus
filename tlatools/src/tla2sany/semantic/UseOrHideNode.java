// Copyright (c) 2007 Microsoft Corporation.  All rights reserved.
// last modified on Fri  3 July 2009 at 12:41:45 PST by lamport 
package tla2sany.semantic;

import java.util.Hashtable;

import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import util.UniqueString;

/***************************************************************************
* This class represents a USE or HIDE statement.  It is of kind            *
* UseKind or HideKind.                                                     *
***************************************************************************/
public class UseOrHideNode extends LevelNode {

  /*************************************************************************
  * The fields.                                                            *
  *                                                                        *
  * A use or hide has the syntax USE/HIDE [facts] [DEF[S] defs].  The      *
  * following two fields are the semantic nodes for the facts and defs.    *
  *************************************************************************/
  public LevelNode[]  facts = null ;  
    /***********************************************************************
    * For each i, facts[i] will be either an ExprNode, a ModuleNode, or    *
    * an OpDefNode of type ModuleInstanceKind (with no parameters).  A     *
    * proof management tool will probably put restrictions on the class    *
    * of expressions that can be used as facts.                            *
    *                                                                      *
    * 4 Mar 2009: implemented a restriction that arbitrary expressions     *
    * can't be used as facts.  The only allowable expressions are the      *
    * names of theorems, assumptions, and steps.                           *
    ***********************************************************************/
  public SymbolNode[] defs  = null ;
    /***********************************************************************
    * For each i, defs[i] should be a UserDefinedOpDefKind or              *
    * ModuleInstanceKind OpDefNode or a ThmOrAssumpDefNode                 *
    ***********************************************************************/

  public boolean isOnly ;
    /***********************************************************************
    * True iff this node was formed from an "ONLY" step.  This is          *
    * possible only if the node is of kind UseKind or if it was            *
    * temporarily constructed for making a LeafProofNode for a "BY ONLY"   *
    * proof.  However, the "ONLY BY" construct might be disabled.          *
    ***********************************************************************/
    
  /**
   * If the UseOrHideNode is a proof step, this is the step number.  It
   * is made a UniqueString for consistency; there's no need to make
   * comparison efficient.
   * Added by LL on 6 June 2010.
   */
  private UniqueString stepName = null;

    public void setStepName(UniqueString stepName)
    {
        this.stepName = stepName;
    }

    /**
     * @return the stepName
     */
    public UniqueString getStepName()
    {
        return stepName;
    }
  /*************************************************************************
  * The constructor.                                                       *
  *************************************************************************/
  public UseOrHideNode(int kind, TreeNode stn, LevelNode[] theFacts, 
                   SymbolNode[] theDefs, boolean only) {
    super(kind, stn) ;
    this.facts = theFacts ;
    this.defs = theDefs ;
    this.isOnly = only ;
  } ;
  
  /*************************************************************************
  * The following method was added 4 Mar 2009 to check the restriction     *
  * that only the names of facts (and of modules) can be used as facts in  *
  * a USE or HIDE.                                                         *
  *                                                                        *
  * It was modified on 1 Jul 2009 to allow the use of expressions as       *
  * facts in a USE.                                                        *
  *************************************************************************/
  public void factCheck() {
    if (this.facts == null || this.getKind() == UseKind) { return; };
    for (int i = 0; i < this.facts.length; i++) {
      if (    (this.facts[i].getKind() == OpApplKind) 
           && (((OpApplNode) this.facts[i]).operator.getKind() 
                   != ThmOrAssumpDefKind)) {
          errors.addError(
             this.facts[i].stn.getLocation(),
               "The only expression allowed as a fact in a HIDE " +
               "is \nthe name of a theorem, assumption, or step.");
      } ;
    } // for
  }

  public boolean levelCheck(int iter) { 
    /***********************************************************************
    * Level checking is performed by level-checking the facts.  Since the  *
    * defs should be defined operators, they have already been level       *
    * checked.                                                             *
    ***********************************************************************/
    if (this.levelChecked >= iter) return this.levelCorrect;
    return this.levelCheckSubnodes(iter, facts) ;
   }

  public void walkGraph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);
    if (semNodesTable.get(uid) != null) return;
    semNodesTable.put(new Integer(myUID), this);
    for (int  i = 0; i < facts.length; i++) {
      facts[i].walkGraph(semNodesTable);
      } ;
    /***********************************************************************
    * Note: there's no need to walk the defs array because all the nodes   *
    * on it are walked from the nodes under which they appear.             *
    ***********************************************************************/
   }

  /*
   * The children are the facts.
   * @see tla2sany.semantic.SemanticNode#getChildren()
   */
  public SemanticNode[] getChildren() {
      if (this.facts == null || this.facts.length == 0) {
          return null;
      }
      SemanticNode[] res = new SemanticNode[this.facts.length];
      for (int i = 0; i < facts.length; i++) {
          res[i] = facts[i];
      }
      return res;
   }
  
  public String toString(int depth) {
    if (depth <= 0) return "";
    String ret = "\n*UseOrHideNode:\n"
                  + super.toString(depth)
                  + Strings.indent(2, "\nisOnly: " + this.isOnly) 
                  + Strings.indent(2, "\nfacts:") ;
    for (int i = 0 ; i < this.facts.length; i++) {
        ret += Strings.indent(4, this.facts[i].toString(1)) ;
      } ;
    ret += Strings.indent(2, "\ndefs:") ;
    for (int i = 0 ; i < this.defs.length; i++) {
        ret += Strings.indent(4, this.defs[i].toString(1)) ;
      } ;
    return ret;
   }

}
