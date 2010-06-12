// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;

import tla2sany.explorer.ExploreNode;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.utilities.Vector;

public class LetInNode extends ExprNode
implements ExploreNode, LevelConstants {

  /**
   * This node represents a LET expression, for example 
   *
   * LET Foo(a) == a + x 
   *     Bar == Foo(a) + a 
   * IN body 
   */

  private SymbolNode[] opDefs;
  public Context context;
    /***********************************************************************
    * opDefs is an array of the OpDefNode and ThmOrAssumpDefNode objects   *
    * defined in the LET. For TLA+1, these LET definitions were never      *
    * visible outside the IN expression.  The only reason for remembering  *
    * them was for level checking and printing them out.  Since in TLA+2   *
    * the definitions can be referred to from outside the IN expression,   *
    * the Context `context' was added that captures everything in the      *
    * LET, including ModuleInstanceKind OpDef nodes, and allows            *
    * convenient name lookup of them.  However, to minimize changes and    *
    * the possibility that allows for errors, the opDefs field has been    *
    * maintained.                                                          *
    ***********************************************************************/
  private InstanceNode[] insts;
    /***********************************************************************
    * Like opDefs, except for the OpDef nodes of kind ModuleInstanceKind.  *
    * Used only for level checking.                                        *
    ***********************************************************************/
  private ExprNode body;

  /* Constructor */
  public LetInNode(TreeNode             treeNode, 
                   SymbolNode[]          defs, 
                   InstanceNode[]       insts,
                   ExprNode bdy, 
                   Context ctext) {
    super(LetInKind, treeNode);
    this.opDefs = defs;
    this.insts = insts;
    this.body = bdy;
    this.context = ctext;
  }

  /**
   * Return the array of LET operator definitions. In the example above,
   * getLets()[1] is the OpDefNode representing the definition of Bar.
   */
  /*************************************************************************
  * The following method is not used by the parser and was provided for    *
  * use by tools.  It is no longer needed, since tools, can obtain that    *
  * information from the (public) context field.  However, TLC uses it,    *
  * until it is changed, we must provide it.  Since opDefs was changed to  *
  * include both ThmOrAssumpDefNode objects and ModuleInstanceKind         *
  * OpDefNode objects, it must be reimplemented.                           *
  *************************************************************************/
  private OpDefNode[] gottenLets = null ;
  public final OpDefNode[] getLets() { 
    if (gottenLets == null) {
      /*********************************************************************
      * First count how many UserDefinedOpKind OpDefNode objects are in    *
      * opDefs.                                                            *
      *********************************************************************/
      int cnt = 0 ;
      for (int i = 0 ; i < opDefs.length ; i++) {
        if (opDefs[i].getKind() == UserDefinedOpKind) {cnt++;} ;
       }
      gottenLets = new OpDefNode[cnt] ;
      cnt = 0 ;
      for (int i = 0 ; i < opDefs.length ; i++) {
        if (opDefs[i].getKind() == UserDefinedOpKind) {
          gottenLets [cnt] = (OpDefNode) opDefs[i] ;
          cnt++;} ;
       }
      
     }  
    return this.gottenLets; 
    }

  /* Return the body of the LET expression (the IN expression). */
  public final ExprNode getBody() { return this.body; }

  /* Level checking */
// These fields are now part of all LevelNode subclasses.
//  private boolean levelCorrect;
//  private int level;
//  private HashSet levelParams; 
//  private SetOfLevelConstraints levelConstraints;
//  private SetOfArgLevelConstraints argLevelConstraints;
//  private HashSet argLevelParams;

  public final boolean levelCheck(int itr) {
    if (this.levelChecked >= itr) return this.levelCorrect;
    levelChecked = itr ;

    // Level check all the components:
    this.levelCorrect = true;
    for (int i = 0; i < this.opDefs.length; i++) {
    /***********************************************************************
    * In TLA+2, opDefs contains ModuleInstanceKind OpDefNode objects,      *
    * which should not be level checked.  (They have no body to level      *
    * check.)                                                              *
    ***********************************************************************/
      if (   (this.opDefs[i].getKind() != ModuleInstanceKind)
          && !this.opDefs[i].levelCheck(itr)) {
        this.levelCorrect = false;
      }
    }
    if (!this.body.levelCheck(itr)) {
      this.levelCorrect = false;
    }
    for (int i = 0; i < this.insts.length; i++) {
      if (!this.insts[i].levelCheck(itr)) {
        this.levelCorrect = false;
      }
    }

    // Calculate level information:
    this.level = this.body.getLevel();

    /***********************************************************************
    * 23 February 2009: Added ".clone" to the following statements.  I     *
    * don't think this is needed and that everything works fine despite    *
    * the aliasing of the levelParams and allParams fields of this node    *
    * and its body to the same HashSets, but it doesn't hurt to be safe.   *
    ***********************************************************************/
    this.levelParams = (HashSet) this.body.getLevelParams().clone();
    this.allParams   = (HashSet) this.body.getAllParams().clone();

//    this.levelConstraints = new SetOfLevelConstraints();
    this.levelConstraints.putAll(this.body.getLevelConstraints());
    for (int i = 0; i < this.opDefs.length; i++) {
      if (this.opDefs[i].getKind() != ModuleInstanceKind) {
         this.levelConstraints.putAll(opDefs[i].getLevelConstraints());} ;
        /*******************************************************************
        * opDefs[i] is level checked above.                                *
        *******************************************************************/
    }

//    this.argLevelConstraints = new SetOfArgLevelConstraints();
    this.argLevelConstraints.putAll(this.body.getArgLevelConstraints());
    for (int i = 0; i < this.opDefs.length; i++) {
      if (this.opDefs[i].getKind() != ModuleInstanceKind) {
        this.argLevelConstraints.putAll(opDefs[i].getArgLevelConstraints());} ;
    }

//    this.argLevelParams = new HashSet();
    this.argLevelParams.addAll(this.body.getArgLevelParams());
    for (int i = 0; i < this.opDefs.length; i++) {
      if (this.opDefs[i].getKind() != ModuleInstanceKind) {
        /*******************************************************************
        * opDefs[i] is either an OpDefNode or a ThmOrAssumpDefNode; only   *
        * an OpDefNode can have parameters.                                *
        *******************************************************************/
        FormalParamNode[] params = new FormalParamNode[0] ;
        if (this.opDefs[i].getKind() != ThmOrAssumpDefKind){
          params = ((OpDefNode) this.opDefs[i]).getParams();
          } ;
        Iterator iter = this.opDefs[i].getArgLevelParams().iterator();
        while (iter.hasNext()) {
          ArgLevelParam alp = (ArgLevelParam)iter.next();
          if (!alp.occur(params)) {
            this.argLevelParams.add(alp);
          }
         }
       }
    }
    for (int i = 0; i < this.insts.length; i++) {
      this.argLevelParams.addAll(this.insts[i].getArgLevelParams());
        /*******************************************************************
        * insts[i] level checked above.                                    *
        *******************************************************************/
     }
    return this.levelCorrect;
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
//  public final HashSet getArgLevelParams() { 
//    return this.argLevelParams; 
//  }

  /**
   * toString, levelDataToString, and walkGraph methods to implement
   * ExploreNode interface
   */
//  public final String levelDataToString() { 
//    return "Level: "               + this.level               + "\n" +
//           "LevelParameters: "     + this.levelParams         + "\n" +
//           "LevelConstraints: "    + this.levelConstraints    + "\n" +
//           "ArgLevelConstraints: " + this.argLevelConstraints + "\n" +
//           "ArgLevelParams: "      + this.argLevelParams      + "\n" ;
//  }

  public SemanticNode[] getChildren() {
      SemanticNode[] res = 
         new SemanticNode[this.opDefs.length + this.insts.length + 1];
      res[res.length-1] = this.body;
      int i;
      for (i = 0; i < this.opDefs.length; i++) {
          res[i] = this.opDefs[i];
      }
      for (int j = 0; j < this.insts.length; j++) {
          res[i+j] = this.insts[j];
      }
      return res;
   }
  
  public final void walkGraph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);

    if (semNodesTable.get(uid) != null) return;

    semNodesTable.put(new Integer(myUID), this);

    /***********************************************************************
    * Can now walk LET nodes from context, don't need to use opDefs        *
    * (which is incomplete).                                               *
    ***********************************************************************/
    if (context != null){context.walkGraph(semNodesTable);} ;
//    if (opDefs != null) {
//      for (int i = 0; i < opDefs.length; i++) {
//        if (opDefs[i] != null) opDefs[i].walkGraph(semNodesTable);
//      }
//    }
    if (body != null) body.walkGraph(semNodesTable);
  }

  public final String toString(int depth) {
    if (depth <= 0) return "";

    String ret = "\n*LetInNode: " + super.toString(depth);
    /***********************************************************************
    * Print context.                                                       *
    ***********************************************************************/
    Vector contextEntries = context.getContextEntryStringVector(1,false);
      /*********************************************************************
      * The depth argument 1 of getContextEntryStringVector causes only    *
      * the name and node uid of the entry and not the node itself to be   *
      * printed.                                                           *
      *********************************************************************/
    if (contextEntries != null) {
      for (int i = 0; i < contextEntries.size(); i++) {
        if (contextEntries.elementAt(i) != null) {
          ret += Strings.indent(2, (String)contextEntries.elementAt(i));
        }
        else {
          ret += "*** null ***"; };
        } ;
      } ;

    /***********************************************************************
    * We no longer print opDefs because the information is in the context. *
    ***********************************************************************/
//    for (int i = 0; i < opDefs.length; i++) {
//      ret += Strings.indent(2,"\nDef:" + Strings.indent(2, opDefs[i].toString(depth-1)));
//    }
    ret += Strings.indent(2, "\nBody:" + Strings.indent(2, body.toString(depth-1)));
    return ret;
  }

}
