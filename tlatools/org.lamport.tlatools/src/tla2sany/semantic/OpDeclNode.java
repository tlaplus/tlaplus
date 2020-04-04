// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

// last modified on Sat 28 June 2008 at  0:39:10 PST by lamport

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
 * An OpDeclNode can have one of the following kinds:
 *
 *     ConstantDeclKind
 *        Represents a constant declaration, such as the C in
 *        CONSTANTS B, C, D
 *
 *     VariableDeclKind
 *        Represents a variable declaration, such as the y in
 *        VARIABLES x, y, z
 *
 *     BoundSymbolKind
 *        Represents a bound symbol such as the b in \E a, b \in S : P
 */
/***************************************************************************
* Additional kinds added by LL on 22 Mar 2007:                             *
*                                                                          *
*   NewConstantKind                                                        *
*   NewVariableKind                                                        *
*   NewStateKind                                                           *
*   NewActionKind                                                          *
*   NewTemporalKind                                                        *
*                                                                          *
* Each represents a declaration in the ASSUME part of an ASSUME/PROVE.     *
***************************************************************************/

public class OpDeclNode extends OpDefOrDeclNode {

// Now a field in all subclasses of LevelNode
//  private int level;

  /*************************************************************************
  * The constructor.                                                       *
  *************************************************************************/
  public OpDeclNode(UniqueString us, int kind, int level,
		    int arity, ModuleNode mn, SymbolTable symbolTable,
                    TreeNode stn) {
    super(us, kind, arity, mn, symbolTable, stn);
    this.level = level;
    if (this.getKind() == ConstantDeclKind) {
      this.levelParams.add(this);
      this.allParams.add(this);} ;
    this.levelChecked = 1;
    if (st != null) {
      st.addSymbol(us, this);
    }
  }

  /**
   * Constants and variables are never declared to be LOCAL
   * Their scope may *be* local (as with LET, or bound variables, or
   * in inner modules), but the LOCAL modifier is not used.
   */
  public final boolean isLocal() { return false; }

  public final int getArity() { return this.arity; }

  public final boolean match(OpApplNode oa, ModuleNode mn) {
    ExprOrOpArgNode[] args = oa.getArgs();

    if (args == null || arity != args.length) {
      errors.addError(oa.getTreeNode().getLocation(),
		      "Operator used with the wrong number of arguments.");
      return false;
    }
    return true;
  }

  /* Level checking */

//  private HashSet levelParams;

  @Override
  public final boolean levelCheck(int iter) {
    /***********************************************************************
    * Level information set by constructor.                                *
    ***********************************************************************/
//    if (levelChecked > 0) { return true ;} ;
//    levelChecked = iter;
//    /***********************************************************************
//    * Note: level set by constructor.                                      *
//    ***********************************************************************/
//    if (this.getKind() == ConstantDeclKind) {this.levelParams.add(this);} ;
    return true;
   }


//  public final int getLevel() { return this.level; }
//
//  public final HashSet getLevelParams() {
//    if (this.levelParams == null) {
//      if (this.getKind() == ConstantDeclKind) {
//	this.levelParams = new HashSet();
//	this.levelParams.add(this);
//      }
//      else {
//	this.levelParams = EmptySet;
//      }
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
   * walkGraph, levelDataToString, and toString methods to implement
   * ExploreNode interface
   */
//  public final String levelDataToString() {
//    return "Level: "               + this.level                    + "\n" +
//           "LevelParameters: "     + this.getLevelParams()         + "\n" +
//           "LevelConstraints: "    + this.getLevelConstraints()    + "\n" +
//           "ArgLevelConstraints: " + this.getArgLevelConstraints() + "\n" +
//           "ArgLevelParams: "      + this.getArgLevelParams()      + "\n";
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
	public String getHumanReadableImage() {
		if (getKind() == 2) {
			return super.getName().toString() + " CONSTANT";
		} else if (getKind() == 3) {
			return super.getName().toString() + " VARIABLE";
		}
		return super.getHumanReadableImage();
	}

  @Override
  public final String toString (int depth) {
    if (depth <= 0) return "";
    return "\n*OpDeclNode: " + this.getName() + "  " + super.toString(depth)
           + "\n  originallyDefinedInModule: " +
                            (originallyDefinedInModule != null
                             ? originallyDefinedInModule.getName().toString()
                             : "<null>" ) ;
  }


  protected String getNodeRef() {
    return "OpDeclNodeRef";
  }

  protected Element getSymbolElement(Document doc, SymbolContext context) {
    Element e = doc.createElement("OpDeclNode");
    e.appendChild(appendText(doc,"uniquename",getName().toString()));
    e.appendChild(appendText(doc,"arity",Integer.toString(getArity())));
    e.appendChild(appendText(doc,"kind", Integer.toString(getKind())));
    return e;
  }
}
