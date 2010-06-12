// Copyright (c) 2007 Microsoft Corporation.  All rights reserved.

// last modified on Fri 23 Nov 2007 at 17:21:52 PST by lamport
/***************************************************************************
* The NewSymbNode constructor is invoked in semantic/Generator.java to     *
* construct the nodes corresponding to a NewSymb syntactic node in an      *
* AssumeProve.  The NewSymb node represents a declaration in an ASSUME,    *
* such as "ASSUME CONSTANT x \in S ".                                      *
*                                                                          *
* The node has two descendants in the semantic tree, returned              *
* by these methods:                                                        *
*   OpDeclNode getOpDeclNode()                                             *
*     An OpDeclNode for the declaration.                                   *
*                                                                          *
*   ExprNode getSet()                                                      *
*     If the node represents a declaration such as "CONSTANT x \in S",     *
*     then this returns the ExprNode for S. Otherwise, it returns null.    *
***************************************************************************/

package tla2sany.semantic;

import java.util.Hashtable;

import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;


public class NewSymbNode extends LevelNode {

  /*************************************************************************
  * Fields.                                                                *
  *************************************************************************/
  private OpDeclNode opDeclNode = null;
    /***********************************************************************
    * The OpDeclNode for the declaration represented by the NewSymbNode    *
    * object.                                                              *
    ***********************************************************************/
  private ExprNode  set         = null;
    /***********************************************************************
    * The ExprNode for expression S in "CONSTANT id \in S".                *
    ***********************************************************************/
// There's now a level field for all LevelNode subclasses, and this.levelChecked 
// indicates if levelCheck has been callsed
//  private int       level = -1;  
//    /***********************************************************************
//    * The level.  The value of -1 indicates that levelCheck has not yet    *
//    * been called.                                                         *
//    ***********************************************************************/

// Role subsumed by this.levelCorrect
//  private boolean  theLevelCheck = true ;
//    /***********************************************************************
//    * Set by this.levelCheck to the value to be returned on subsequent     *
//    * calls.                                                               *
//    ***********************************************************************/
    
  /*************************************************************************
  * The Constructor.                                                       *
  *************************************************************************/
  public NewSymbNode(
           OpDeclNode   opDeclNode, // The OpDeclNode for the declaration.
           ExprNode     set,        // Expression S in "CONSTANT x \in S", 
                                    //   null for other kinds of declaration.
           TreeNode stn             // The syntax node.
          ) {
    super(NewSymbKind, stn) ;
    this.set        = set;
    this.opDeclNode = opDeclNode ;
  }   


  /*************************************************************************
  * Methods particular to the NewSymb node.                                *
  *************************************************************************/
  public final ExprNode   getSet()         {return set;}
  public final OpDeclNode getOpDeclNode() {return opDeclNode;}
  
  /*************************************************************************
  * The implementation of the LevelNode abstract methods.                  *
  *                                                                        *
  * The level of the node is the maximum of opDeclNode's level and the     *
  * level of the `set' expression, if it's non-null.  Any other level      *
  * information comes from the `set' expression.                           *
  *************************************************************************/
  public boolean levelCheck(int iter)       {

    if (levelChecked < iter) {
      /*********************************************************************
      * This is the first call of levelCheck, so the level information     *
      * must be computed.  Actually, with the current implementation,      *
      * there's no need to call opDeclNode.levelCheck, since that just     *
      * returns true.  However, we do it anyway in case the OpDeclNode     *
      * class is changed to make levelCheck do something.                  *
      *********************************************************************/
      levelChecked = iter ;
      boolean opDeclLevelCheck = opDeclNode.levelCheck(iter) ;
      level = opDeclNode.getLevel() ;
      if (set != null) { 
        levelCorrect = set.levelCheck(iter) ;
        level = Math.max(set.getLevel(), level);
        if (level == TemporalLevel) {
          levelCorrect = false; 
          errors.addError(this.stn.getLocation(),
                          "Level error:\n" + 
                          "Temporal formula used as set.");
          }
       }  ;
      levelCorrect = levelCorrect && opDeclLevelCheck;
      if (set != null) {
        levelParams = set.getLevelParams(); 
        allParams = set.getAllParams(); 
        levelConstraints = set.getLevelConstraints(); 
        argLevelConstraints = set.getArgLevelConstraints();
        argLevelParams      = set.getArgLevelParams();
       }; // if (set != null) 
      }; // if (levelChecked < iter)
    return levelCorrect;
   }
    
//  public int getLevel()             {return this.level; }
//
//  public HashSet getLevelParams()   {
//    if (set == null) {return EmptySet;}
//    else return set.getLevelParams();
//   }
//
//  public SetOfLevelConstraints getLevelConstraints() {
//    if (set == null) {return EmptyLC;}
//    else return set.getLevelConstraints();
//   }
//
//  public SetOfArgLevelConstraints getArgLevelConstraints() {
//    if (set == null) {return EmptyALC;}
//    else return set.getArgLevelConstraints();
//   }
//
//  public HashSet getArgLevelParams() {
//    if (set == null) {return EmptySet;}
//    else return set.getArgLevelParams();
//   }

  /** 
   * toString, levelDataToString and walkGraph methods to implement
   * ExploreNode interface
   */
//  public final String levelDataToString() { 
//    return "Level: "               + this.level                    + "\n" +
//           "LevelParameters: "     + this.getLevelParams()         + "\n" +
//           "LevelConstraints: "    + this.getLevelConstraints()    + "\n" +
//           "ArgLevelConstraints: " + this.getArgLevelConstraints() + "\n" +
//           "ArgLevelParams: "      + this.getArgLevelParams()      + "\n";
//  }

  /**
   * The body is the node's only child.
   */
  
  public SemanticNode[] getChildren() {
    if (this.set == null) {
        return null;
    } else {
      return new SemanticNode[] {this.set};
    }
  }
 
  public final void walkGraph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);
    if (semNodesTable.get(uid) != null) return;
    semNodesTable.put(new Integer(myUID), this);
    if (set != null) { set.walkGraph(semNodesTable); } ;
   }

  public final String toString(int depth) {
    if (depth <= 0) return "";
    String setString = "" ;
    if (this.set != null) {
      setString = Strings.indent(2, 
                   "\nSet:" + Strings.indent(2, this.set.toString(depth-1)));
     }
    return "\n*NewSymbNode: " + 
	    "  " + super.toString(depth) + 
             Strings.indent(2, "\nKind: " + this.getKind() +
                          "\nopDeclNode:" + Strings.indent(2, 
                                this.opDeclNode.toString(depth-1)) +
             setString);
   }
}
