// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.Hashtable;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.xml.SymbolContext;
import util.UniqueString;

/**
 * A FormalParamNode represents a formal parameter in a user
 * definition--for example, p and q in
 *
 *    Foo(p, q(_)) == expr
 */
/***************************************************************************
* The constructor adds the node to the SymbolTable specified as an         *
* argument.                                                                *
***************************************************************************/
public class FormalParamNode extends SymbolNode {

  private int          arity;
    // arity of the parameter; 0 for ordinary param; >0 for operator param
  private ModuleNode   moduleNode;
    // the module in which this formal param was declared

  // Constructor
  public FormalParamNode(UniqueString us, int ar, TreeNode stn,
			 SymbolTable symbolTable, ModuleNode mn) {
    super(FormalParamKind, stn, us);
    this.arity      = ar;
    this.moduleNode = mn;
    if (symbolTable != null)     // null for fake formal params of built-in operators
       symbolTable.addSymbol(us, (SymbolNode)this );
  }

  /**
   * Returns the number of arguments this paramter takes when used in
   * an expression.
   */
  public final int getArity() { return this.arity; }

  /* Returns true always.  */
  public final boolean isLocal() { return true; }

  public final ModuleNode getModuleNode() { return this.moduleNode; }

  public final boolean match( OpApplNode test, ModuleNode mn ) {
    /***********************************************************************
    * True iff the current object has the same arity as the node operator  *
    * of the OpApplNode test.                                              *
    ***********************************************************************/
    SymbolNode odn = test.getOperator();
    return odn.getArity() == this.arity;
  }

  public final boolean match(SemanticNode test) {
    /***********************************************************************
    * This weird method does not seem to be used.                          *
    ***********************************************************************/
    return ( this.arity == 0 );
  }

  /* Level checking */
//  private HashSet levelParams;

  @Override
  public final boolean levelCheck(int iter) {
    if (levelChecked == 0) {
      /*********************************************************************
      * There's never any need to do this more than once.                  *
      *********************************************************************/
      levelChecked = iter;
      this.levelParams.add(this);
      this.allParams.add(this);
     } ;
    return true;
   }

//  public final int getLevel() { return ConstantLevel; }
//
//  public final HashSet getLevelParams() {
//    if (this.levelParams == null) {
//      this.levelParams = new HashSet();
//      this.levelParams.add(this);
//    }
//    return this.levelParams;
//  }
//
//  public final SetOfLevelConstraints getLevelConstraints() {
//    return EmptyLC;
//  }
//
//  public final SetOfArgLevelConstraints getArgLevelConstraints() {
//    return EmptyALC;
//  }
//
//  public final HashSet getArgLevelParams() { return EmptySet; }

  /**
   * toString, levelDataToString and walkGraph methods to implement
   * ExploreNode interface
   */
//  public final String levelDataToString() {
//    return "Level: "               + this.getLevel()               + "\n" +
//           "LevelParameters: "     + this.getLevelParams()         + "\n" +
//           "LevelConstraints: "    + this.getLevelConstraints()    + "\n" +
//           "ArgLevelConstraints: " + this.getArgLevelConstraints() + "\n" +
//           "ArgLevelParams: "      + this.getArgLevelParams()      + "\n" ;
//  }

  @Override
  public final void walkGraph(Hashtable<Integer, ExploreNode> semNodesTable, ExplorerVisitor visitor) {
    Integer uid = Integer.valueOf(myUID);
    if (semNodesTable.get(uid) != null) return;

    semNodesTable.put(uid, this);
    visitor.preVisit(this);
    visitor.postVisit(this);
  }

  @Override
  public final String toString(int depth) {
    if (depth <= 0) return "";
    return ("\n*FormalParamNode: " + this.getName().toString() +
	    "  " + super.toString(depth) + "  arity: " + arity);
  }

  protected String getNodeRef() {
    return "FormalParamNodeRef";
  }

  protected Element getSymbolElement(Document doc, SymbolContext context) {
    Element e = doc.createElement("FormalParamNode");
    e.appendChild(appendText(doc,"uniquename",getName().toString()));
    e.appendChild(appendText(doc,"arity",Integer.toString(getArity())));
    return e;
  }
}
