// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// last modified on Fri 23 Nov 2007 at 17:18:39 PST by lamport

package tla2sany.semantic;

import java.util.Hashtable;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.st.TreeNode;
import tla2sany.xml.SymbolContext;
import util.UniqueString;

/**
 * This class represents operators of arity > 0 used as arguments to
 * other operators.  Such operator instances are used in syntactic
 * positions where expressions would usually occur, i.e. as arguments
 * to operators or as the RHS of a substitution involved in module
 * instantiation.
 */

public class OpArgNode extends ExprOrOpArgNode {

  private SymbolNode   op;      // The OpDefNode, OpDeclNode, or
                                // FormalParamNode corresponding to
                                // THIS OpArgNode
  private UniqueString name;    // The string name of the full compound
                                // name of this operator
  private int          arity;   // The correct arity for this operator
  private ModuleNode   mn;      // the Module in which THIS OpArgNode appears

  /* Used only for construction of a "null" OpArg */
  public OpArgNode(UniqueString name) {
    super(OpArgKind, SyntaxTreeNode.nullSTN);
    this.name = name;
    this.arity = -2;
  }

  /**
   * The primary constructor; we allow for the case that op may be
   * null because in the case of some kind of semantic error
   * (unresolved symbol) we want to be able to continue semantic
   * analysis.
   */
  public OpArgNode(SymbolNode op, TreeNode stn, ModuleNode mn)
  throws AbortException {
    super(OpArgKind, stn);

    // if op is an OpDefNode, OpDeclNode, or FormalParamNode
    this.op        = op;
    this.name      = op.getName();
    this.arity     = op.getArity();
    this.mn        = mn;
  }

  public final SymbolNode   getOp()        { return this.op; }

  public final int          getArity()     { return this.arity; }

  public final UniqueString getName()      { return this.name; }

  public final ModuleNode   getModule()    { return this.mn; }

  /* Level check */
  @Override
  public final boolean levelCheck(int iter) {
    if (levelChecked >= iter) {return this.levelCorrect; } ;
    levelChecked = iter ;
    levelCorrect        = op.levelCheck(iter) ;
    level               = op.getLevel();
    levelParams         = op.getLevelParams();
    allParams           = op.getAllParams();
    levelConstraints    = op.getLevelConstraints();
    argLevelConstraints = op.getArgLevelConstraints();
    argLevelParams      = op.getArgLevelParams();
    return levelCorrect ;
  }

//  public final int getLevel() { return this.op.getLevel(); }
//
//  public final HashSet getLevelParams() {
//    return this.op.getLevelParams();
//  }
//
//  public final SetOfLevelConstraints getLevelConstraints() {
//    return this.op.getLevelConstraints();
//  }
//
//  public final SetOfArgLevelConstraints getArgLevelConstraints() {
//    return this.op.getArgLevelConstraints();
//  }
//
//  public final HashSet getArgLevelParams() {
//    return this.op.getArgLevelParams();
//  }

  /**
   * walkGraph, levelDataToString, and toString methods to implement
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

    /***********************************************************************
    * Modified on 28 Mar 2007 by LL to walk the operator node of the       *
    * current OpArgNode.  This is apparently necessary only if the         *
    * operator node is an OpDefNode representing a lambda                  *
    * expression--otherwise, the operator node will have been walked when  *
    * walking the node representing the declaration or definition of the   *
    * operator.                                                            *
    ***********************************************************************/
    if (op != null) {op.walkGraph(semNodesTable, visitor) ;} ;
    visitor.postVisit(this);
  }

  @Override
  public final String toString(int depth) {
    if (depth <= 0) return "";

    return "\n*OpArgNode: " + ( name != null ? name.toString() : "null") +
      "  " + super.toString(depth) +
      "  arity: " + arity +
      "  op: " + (op != null ? "" + ((SemanticNode)op).getUid() : "null" );
  }

  @Override
  protected Element getLevelElement(Document doc, SymbolContext context) {
    Element e = doc.createElement("OpArgNode");
    Element n = doc.createElement("argument");
    //Element ope = op.getSymbolElement(doc, context);
    Element ope = op.export(doc, context);
    n.appendChild(ope);
    e.appendChild(n);

    //e.appendChild(appendText(doc,"uniquename",getName().toString()));
    //e.appendChild(appendText(doc,"arity", Integer.toString(getArity())));

    return e;
  }
}
