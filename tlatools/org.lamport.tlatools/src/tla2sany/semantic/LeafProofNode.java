// Copyright (c) 2007 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.Hashtable;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.xml.SymbolContext;

/***************************************************************************
* This class represents a leaf proof.  It is of kind LeafProffKind         *
***************************************************************************/
public class LeafProofNode extends ProofNode {

  /*************************************************************************
  * The fields.                                                            *
  *                                                                        *
  * A leaf proof has the syntax                                            *
  *                                                                        *
  *   [PROOF]   BY [ONLY] [facts] [DEF[S] defs].                           *
  *           | OBVIOUS                                                    *
  *           | OMITTED                                                    *
  *                                                                        *
  * The following two fields are the semantic nodes for the facts and      *
  * defs.                                                                  *
  *************************************************************************/
  LevelNode[]  facts = null ;
    /***********************************************************************
    * For each i, facts[i] will be either an ExprNode, a ModuleNode, or    *
    * an OpDefNode of type ModuleInstanceKind (with no parameters).  A     *
    * proof management tool will probably put restrictions on the class    *
    * of expressions that can be used as facts.                            *
    ***********************************************************************/
  SymbolNode[] defs  = null ;
    /***********************************************************************
    * For each i, defs[i] should be a UserDefinedOpDefKind or              *
    * ModuleInstanceKind OpDefNode or a ThmOrAssumpDefNode                 *
    ***********************************************************************/
  boolean omitted ;
    /***********************************************************************
    * True iff this is a "[PROOF] OMITTED" statement.  In this case, the   *
    * facts and defs field will be null.  But that is also the case for    *
    * an "OBVIOUS" proof.                                                  *
    ***********************************************************************/
  boolean isOnly ;
    /***********************************************************************
    * True iff this is a "BY ONLY" proof.                                  *
    ***********************************************************************/

  /*************************************************************************
  * The constructor.                                                       *
  *************************************************************************/
  public LeafProofNode(TreeNode stn, LevelNode[] theFacts,
                   SymbolNode[] theDefs, boolean omit, boolean only) {
    super(LeafProofKind, stn) ;
    this.facts   = theFacts ;
    this.defs    = theDefs ;
    this.omitted = omit ;
    this.isOnly = only ;
   } ;


  /*************************************************************************
  * Methods that return the values of the fields.                          *
  *************************************************************************/
  public LevelNode[]  getFacts() {return facts ; } ;
  public SymbolNode[] getDefs() {return defs ;} ;
  public boolean getOmitted() {return omitted ;} ;
  public boolean getOnlyFlag() {return isOnly ;} ;

  @Override
  public boolean levelCheck(int iter) {
    /***********************************************************************
    * Level checking is performed by level-checking the facts.  Since the  *
    * defs should be defined operators, they have already been level       *
    * checked.                                                             *
    ***********************************************************************/
    if (this.levelChecked >= iter) return this.levelCorrect;
    return this.levelCheckSubnodes(iter, facts) ;
   }

  /*
   * The children are the facts.
   * @see tla2sany.semantic.SemanticNode#getChildren()
   */
  @Override
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

  @Override
  public void walkGraph(Hashtable<Integer, ExploreNode> semNodesTable, ExplorerVisitor visitor) {
    Integer uid = Integer.valueOf(myUID);
    if (semNodesTable.get(uid) != null) return;
    semNodesTable.put(uid, this);
    visitor.preVisit(this);
    for (int  i = 0; i < facts.length; i++) {
      facts[i].walkGraph(semNodesTable, visitor);
      } ;
    /***********************************************************************
    * Note: there's no need to walk the defs array because all the nodes   *
    * on it are walked from the nodes under which they appear.             *
    ***********************************************************************/
      visitor.postVisit(this);
   }

  @Override
  public String toString(int depth) {
    if (depth <= 0) return "";
    String ret = "\n*LeafProofNode:\n"
                  + super.toString(depth)
                  + Strings.indent(2, "\nfacts:") ;
    for (int i = 0 ; i < this.facts.length; i++) {
        ret += Strings.indent(4, this.facts[i].toString(depth-1)) ;
      } ;
    ret += Strings.indent(2, "\ndefs:") ;
    for (int i = 0 ; i < this.defs.length; i++) {
        ret += Strings.indent(4, this.defs[i].toString(depth-1)) ;
      } ;
    ret += Strings.indent(2, "\nomitted: " + this.omitted)
            + Strings.indent(2, "\nonlyFlag: " + this.isOnly);
    return ret;
   }

  @Override
  protected Element getLevelElement(Document doc, SymbolContext context) {
    Element e;

    if (getOmitted()) {
      e = doc.createElement("omitted");
    }
    else if (getFacts().length == 0 && getDefs().length == 0) {
      e = doc.createElement("obvious");
    }
    else {
      //SemanticNode.SymbolContext context = new SemanticNode.SymbolContext(context2);
      e = doc.createElement("by");

      Element factse = doc.createElement("facts");
      Element definitions = doc.createElement("defs");

      for (int i=0; i<facts.length; i++) factse.appendChild(facts[i].export(doc,context));
      for (int i=0; i<defs.length; i++) definitions.appendChild(defs[i].export(doc,context));

      e.appendChild(factse);
      e.appendChild(definitions);
      if(getOnlyFlag()) e.appendChild(doc.createElement("only"));
      // at the end, we append the context of the symbols used in this node
      //e.appendChild(context.getContextElement(doc));
    }

    return e;
  }

}
