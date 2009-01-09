// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.Hashtable;

import tla2sany.utilities.Strings;

public class AtNode extends ExprNode {

  private OpApplNode exceptRef;           // reference to OpApplNode for the innermost 
                                          //   enclosing $Except operator
  private OpApplNode exceptComponentRef;  // reference to OpApplNode for the innermost
                                          //   enclosing $Pair operator that represents the
                                          //   ExceptComponent in which this occurrence of @ is used

  // Constructor
  public AtNode(OpApplNode er, OpApplNode ecr) {
    super(AtNodeKind, ecr.stn);
    this.exceptRef          = er;
    this.exceptComponentRef = ecr;
  }

  /** 
   * Return reference to the OpApplNode for the $Except operator with
   * which this occurrence of @ is associated.  For @ on the RHS of
   * an ExceptionSpec, that is the immediately enclosing $Except; for
   * other occurences of @ it is one $Except farther up the tree.
   */
  public final OpApplNode getExceptRef() { return this.exceptRef; }

  /** 
   * Return reference to the OpApplNode for the $Pair operator with
   * which this occurrence of @ is associated.  For @ on the RHS of
   * an ExceptionSpec, that is the immediately enclosing ExceptSpec;
   * for other occurences of @ it is one farther up the tree.
   */
  public final OpApplNode getExceptComponentRef() {
    return this.exceptComponentRef;
  }

  /** 
   * Return the expression that is the "base" of the expression that
   * @ stands for.  In the example [ [ f[3] EXCEPT !.h[4] = (@ + @) ]
   * this expression is f[3].  Both AtNodes in this example refer to
   * the SAME node, not just to copies of the same node.
   */
  public final ExprNode getAtBase() {
    return (ExprNode)this.exceptRef.getArgs()[0];
  }

  /**
   * Return the expression that must be used to modify the "base" to
   * create the actual expression that @ stands for.  In the example
   * [ [ f[3] EXCEPT !.h[4] = (@ + @) ] this expression is roughly
   * transcribable as $Seq($StringNode(h), $ExprNode(4)).  Both
   * AtNodes in this example refer to the SAME node, not just to
   * copies of the same node.
   */
  public final OpApplNode getAtModifier() {
    return (OpApplNode)this.exceptComponentRef.getArgs()[0];
  }

  /* Level check */
// These nodes are now part of all LevelNode subclasses.
//  private int level;
//  private HashSet levelParams; 
//  private SetOfLevelConstraints levelConstraints;
//  private SetOfArgLevelConstraints argLevelConstraints;
//  private HashSet argLevelParams;

  public final boolean levelCheck(int iter) {
    if (this.levelChecked >= iter) return true;
    this.levelChecked = iter;
    
    ExprOrOpArgNode[] args = this.exceptRef.getArgs();
    args[0].levelCheck(iter) ;
    this.level = args[0].getLevel();
    for (int i = 1; i < args.length; i++) {
      args[i].levelCheck(iter) ;
      if (args[i] == this.exceptComponentRef) break;
      this.level = Math.max(this.level, args[i].getLevel());
    }

//    this.levelParams = new HashSet();
    this.levelParams.addAll(args[0].getLevelParams());
    this.allParams.addAll(args[0].getAllParams());
    for (int i = 1; i < args.length; i++) {
      if (args[i] == this.exceptComponentRef) break;
      this.levelParams.addAll(args[i].getLevelParams());
      this.allParams.addAll(args[i].getAllParams());
    }

//    this.levelConstraints = new SetOfLevelConstraints();
    this.levelConstraints.putAll(args[0].getLevelConstraints());
    for (int i = 1; i < args.length; i++) {
      if (args[i] == this.exceptComponentRef) break;
      this.levelConstraints.putAll(args[i].getLevelConstraints());
    }

//    this.argLevelConstraints = new SetOfArgLevelConstraints();
    this.argLevelConstraints.putAll(args[0].getArgLevelConstraints());
    for (int i = 1; i < args.length; i++) {
      if (args[i] == this.exceptComponentRef) break;
      this.argLevelConstraints.putAll(args[i].getArgLevelConstraints());
    }

//    this.argLevelParams = new HashSet();
    this.argLevelParams.addAll(args[0].getArgLevelParams());
    for (int i = 1; i < args.length; i++) {
      if (args[i] == this.exceptComponentRef) break;
      this.argLevelParams.addAll(args[i].getArgLevelParams());
    }
    return true;
  }

//  public final int getLevel() { return this.level; }
//
//  public final HashSet getLevelParams() { return this.levelParams; }
//
//  public final SetOfLevelConstraints getLevelConstraints() { 
//    return this.levelConstraints; 
//  }
//  
//  public final SetOfArgLevelConstraints getArgLevelConstraints() { 
//    return this.argLevelConstraints; 
//  }
//  
//  public final HashSet getArgLevelParams() { return this.argLevelParams; }

  /**
   * toString, levelDataToString, & walkGraph methods needed to
   * implement ExploreNode interface
   */
//  public final String levelDataToString() { 
//    return "Level: "               + this.getLevel()               + "\n" +
//           "LevelParameters: "     + this.getLevelParams()         + "\n" +
//           "LevelConstraints: "    + this.getLevelConstraints()    + "\n" +
//           "ArgLevelConstraints: " + this.getArgLevelConstraints() + "\n" +
//           "ArgLevelParams: "      + this.getArgLevelParams()      + "\n";
//  }

  /*
   * walkGraph finds all reachable nodes in the semantic graph
   * and inserts them in the Hashtable semNodesTable for use by the Explorer tool.
   */
  public final void walkGraph(Hashtable h) {
  // Empty because there are no nodes reachable through an AtNode that are not 
  // reachable by other paths through the semantic graph.
  } // end walkGraph()


  /*
   * Displays this node as a String, implementing ExploreNode interface; depth
   * parameter is a bound on the depth of the portion of the tree that is displayed.
   */
  public final String toString(int depth) {
    if (depth <= 0) return "";
    return "\n*AtNode: " + super.toString(depth) +
           Strings.indent(2, "\nExceptRef: " + exceptRef.getUid() + 
                             "\nExceptComponent: " + exceptComponentRef.getUid());
  }

}
