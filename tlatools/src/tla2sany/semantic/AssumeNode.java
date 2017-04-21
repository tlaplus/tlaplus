// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.HashSet;
import java.util.Hashtable;

import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;

import tla2sany.xml.XMLExportable;
import org.w3c.dom.Attr;
import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

/**
 * This class represents an assumption about the constants in a module.
 */

/***************************************************************************
* In SANY1, this class simply extended SemanticNode.  I don't know why,    *
* since level checking was performed on theorems.                          *
***************************************************************************/
public class AssumeNode extends LevelNode {

  ModuleNode  module;
  ExprNode    assumeExpr;
  private ThmOrAssumpDefNode   def;
    /***********************************************************************
    * For a named assumption, that is one of the form                      *
    * "ASSUME foo == ...", this is the ThmOrAssumpDefNode for the          *
    * definition.                                                          *
    ***********************************************************************/

  private boolean isAxiom = false;
    /***********************************************************************
    * True iff this is an AXIOM rather than an ASSUME or ASSUMPTION.       *
    ***********************************************************************/


  public boolean getIsAxiom() {
    return isAxiom;
  }
//  boolean     localness;
//  Assumptions can no longer be local


  /**
 * @param stn
 * @param expr
 * @param mn
 * @param opd
 */
public AssumeNode(TreeNode stn, ExprNode expr, ModuleNode mn,
                     ThmOrAssumpDefNode opd) {
    super(AssumeKind, stn);
    this.assumeExpr = expr;
// Assumptions can no longer be local
//    this.localness = local;
    this.module = mn;
    this.def = opd;
    if(stn.heirs()[0].getImage().equals("AXIOM")){
        isAxiom = true;
    }
    if (opd != null) opd.thmOrAssump = this;

   }

  /* Returns the expression that is the statement of the assumption */
  public final ExprNode getAssume() { return this.assumeExpr; }

  /*************************************************************************
  * Returns the definition, which is non-null iff this is a named          *
  * theorem.                                                               *
  *************************************************************************/
  public final ThmOrAssumpDefNode getDef() {return this.def;};

//  public final boolean isLocal() { return false; }


  /* Level checking */
  int levelChecked = 0 ;
  public final boolean levelCheck(int iter) {
    if (levelChecked >= iter) {return true ;} ;
    levelChecked = iter;
    boolean res = this.assumeExpr.levelCheck(iter);
    if (this.def != null) {res = this.def.levelCheck(iter) && res;};

    // Verify that the assumption is constant level
    if (this.assumeExpr.getLevel() != ConstantLevel) {
      errors.addError(getTreeNode().getLocation(),
                      "Level error: assumptions must be level 0 (Constant), " +
                      "\nbut this one has level " + this.getLevel() + "." );
    }
    /***********************************************************************
    * The following added on 1 Mar 2009.  See                              *
    * LevelNode.addTemporalLevelConstraintToConstants.                     *
    ***********************************************************************/
    if (res) { addTemporalLevelConstraintToConstants(this.levelParams,
                                                     this.levelConstraints);
     };
    return res;
  }

  public final int getLevel() {
    return this.assumeExpr.getLevel();
  }

  public final HashSet getLevelParams() {
    return this.assumeExpr.getLevelParams();
  }

  public final HashSet getAllParams() {
    return this.assumeExpr.getAllParams();
  }

  public final SetOfLevelConstraints getLevelConstraints() {
    return this.assumeExpr.getLevelConstraints();
  }

  public final SetOfArgLevelConstraints getArgLevelConstraints() {
    return this.assumeExpr.getArgLevelConstraints();
  }

  public final HashSet getArgLevelParams() {
    return this.assumeExpr.getArgLevelParams();
  }

  /**
   * toString(), levelDataToString(), and walkGraph() methods
   */
  public final String levelDataToString() {
    return "Level: "               + getLevel()               + "\n" +
           "LevelParameters: "     + getLevelParams()         + "\n" +
           "LevelConstraints: "    + getLevelConstraints()    + "\n" +
           "ArgLevelConstraints: " + getArgLevelConstraints() + "\n" +
           "ArgLevelParams: "      + getArgLevelParams()      + "\n" ;
  }

  /**
   * Displays this node as a String, implementing ExploreNode
   * interface; depth parameter is a bound on the depth of the portion
   * of the tree that is displayed.
   */
  public final String toString (int depth) {
    if (depth <= 0) return "";
    String res =
       Strings.indent(
         2,
         "\n*AssumeNode " + super.toString( depth ) +
//                        "   local: " + localness +
         ((assumeExpr != null)  ?
             Strings.indent(2,assumeExpr.toString(depth-1)) : "" ));
   if (def != null) {
      res = res + Strings.indent(
                      4,
                      "\n def: " +
                      Strings.indent(2, this.def.toString(depth-1)));
     } ;
    return res ;
  }

  /**
   * The assume expression is the node's only child.
   */

  public SemanticNode[] getChildren() {
    return new SemanticNode[] {this.assumeExpr};
  }

  /**
   * walkGraph finds all reachable nodes in the semantic graph and
   * inserts them in the Hashtable semNodesTable for use by the
   * Explorer tool.
   */
  public final void walkGraph (Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);

    if (semNodesTable.get(uid) != null) return;

    semNodesTable.put(uid, this);
    if (assumeExpr != null) {assumeExpr.walkGraph(semNodesTable);} ;
  }

  /* MR: This is the same as SymbolNode.exportDefinition. Exports the actual theorem content, not only a reference.
   */
  public Element exportDefinition(Document doc, tla2sany.xml.SymbolContext context) {
    if (!context.isTop_level_entry())
      throw new IllegalArgumentException("Exporting theorem ref "+getNodeRef()+" twice!");
    context.resetTop_level_entry();
    try {
      Element e = getLevelElement(doc, context);
      // level
      try {
        Element l = appendText(doc,"level",Integer.toString(getLevel()));
        e.insertBefore(l,e.getFirstChild());
      } catch (RuntimeException ee) {
        // not sure it is legal for a LevelNode not to have level, debug it!
      }
      //location
      try {
        Element loc = getLocationElement(doc);
        e.insertBefore(loc,e.getFirstChild());
      } catch (RuntimeException ee) {
        // do nothing if no location
      }
      return e;
    } catch (RuntimeException ee) {
      System.err.println("failed for node.toString(): " + toString() + "\n with error ");
      ee.printStackTrace();
      throw ee;
    }
  }

  protected String getNodeRef() {
    return "AssumeNodeRef";
  }

//  public Element export(Document doc, tla2sany.xml.SymbolContext context) {
//    if (getDef() == null)
//      // we export the definition of the assumption
//      return super.export(doc,context);
//    else
//      // we export its name only, named assumptions will be exported through the ThmOrAss..
//      return getDef().export(doc,context);
//  }

  protected Element getLevelElement(Document doc, tla2sany.xml.SymbolContext context) {
    Element e = doc.createElement("AssumeNode");
    if (def != null) {
      //if there is a definition, export it too
      Node d = doc.createElement("definition");
      d.appendChild(def.export(doc, context));
      e.appendChild(d);
      assert( def.getBody() == this.assumeExpr ); //make sure theorem and definition body agree before export
    }
    Node n = doc.createElement("body");
    n.appendChild(getAssume().export(doc,context));
    e.appendChild(n);
    return e;
  }

  /* overrides LevelNode.export and exports a UID reference instad of the full version*/
  public Element export(Document doc, tla2sany.xml.SymbolContext context) {
    // first add symbol to context
    context.put(this, doc);
    Element e = doc.createElement(getNodeRef());
    e.appendChild(appendText(doc,"UID",Integer.toString(myUID)));
    return e;
  }
}
