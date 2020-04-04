// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.Hashtable;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;

import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.xml.SymbolContext;
import util.UniqueString;



/**
 * This node represents a string literal in the specification--for
 * example "abc".  The only information added to the SemanticNode
 * superclass is the level information and the UniqueString
 * representation of the string.
 */

public class StringNode extends ExprNode implements ExploreNode {

  private UniqueString value;

  public StringNode(TreeNode stn, boolean strip) {
    super(StringKind, stn);

    this.value = stn.getUS();
    if (strip) {
      // Strip off quote marks from image in stn
      String str = this.value.toString();
      str = str.substring(1, str.length()-1);
      this.value = UniqueString.uniqueStringOf(str);
      /*********************************************************************
      * Setting levelChecked shouldn't be necessary.                       *
      *********************************************************************/
//      this.levelChecked = 99 ;
    }
  }

  /**
   * Returns the UniqueString representation of the string.
   */
  public final UniqueString getRep() { return this.value; }

  /* Level Checking */
  @Override
  public final boolean levelCheck(int iter) {
    levelChecked = iter;
      /*********************************************************************
      * Set it just to show that levelCHeck was called.                    *
      *********************************************************************/
    return true;
  }

//  public final int getLevel() { return ConstantLevel; }
//
//  public final HashSet getLevelParams() { return EmptySet; }
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
   * toString, levelDataToString, & walkGraph methods to implement
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

  final String PrintVersion(String str) {
    StringBuffer buf = new StringBuffer(str.length()) ;
    for (int i = 0 ; i < str.length() ; i++) {
      switch (str.charAt(i)) {
        case '\"' :
          buf.append("\\\"") ;
          break ;
        case '\\' :
          buf.append("\\\\") ;
          break ;
        case '\t' :
          buf.append("\\t") ;
          break ;
        case '\n' :
          buf.append("\\n") ;
          break ;
        case '\f' :
          buf.append("\\f") ;
          break ;
        case '\r' :
          buf.append("\\r") ;
          break ;
        default :
          buf.append(str.charAt(i)) ;
          break ;
       } // switch
     }; // for
    return buf.toString();
   }

  @Override
  public final String toString(int depth) {
    if (depth <= 0) return "";
    return "\n*StringNode: " + super.toString(depth)
                             + "Value: '" + PrintVersion(value.toString()) +
                             "'" + " Length: " + value.length();
  }

  @Override
  protected Element getLevelElement(Document doc, SymbolContext context) {
      Element e = doc.createElement("StringValue");
      Node n = doc.createTextNode(value.toString());
      e.appendChild(n);
      return appendElement(doc, "StringNode", e);
   // return appendText(doc,"StringNode",value.toString());
  }
}
