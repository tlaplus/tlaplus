// Copyright (c) 2007 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.Hashtable;

import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;

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
    ***********************************************************************/
  public SymbolNode[] defs  = null ;
    /***********************************************************************
    * For each i, defs[i] should be a UserDefinedOpDefKind or              *
    * ModuleInstanceKind OpDefNode or a ThmOrAssumpDefNode                 *
    ***********************************************************************/

  /*************************************************************************
  * The constructor.                                                       *
  *************************************************************************/
  public UseOrHideNode(int kind, TreeNode stn, LevelNode[] theFacts, 
                   SymbolNode[] theDefs) {
    super(kind, stn) ;
    this.facts = theFacts ;
    this.defs = theDefs ;
   } ;
  
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

  public String toString(int depth) {
    if (depth <= 0) return "";
    String ret = "\n*UseOrHideNode:\n"
                  + super.toString(depth)
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
