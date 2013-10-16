// Last modified on Sun 18 May 2008 at  7:36:43 PST by lamport

/***************************************************************************
* params field changed from OpDeclNode[] to FormalParamNode[] on           *
* 4 July 2007                                                              *
*                                                                          *
* Modified on 18 May 2008 by LL to allow the body to be an AssumeProve     *
* node as well as an OpApplNode.                                           *
***************************************************************************/

/***************************************************************************
* See the warning about labels of instantiated modules in                  *
* semantic/OpDefOrLabelNode.java.                                          *
*                                                                          *
* A LabelNode is an ExprNode that represents a either a labeled            *
* expression or a labeled ASSUME/PROVE. Since an ASSUME/PROVE isn't an     *
* expression, this shouldn't really be an ExprNode.                        *
*                                                                          *
* If the LabelNode comes from the syntax tree node for                     *
*                                                                          *
*    lab(x, y) :: expOrAssumeProve                                         *
*                                                                          *
* it has the following fields                                              *
*                                                                          *
*    name : the UniqueString for "lab"                                     *
*                                                                          *
*    params : An array of FormalParamNode containing the nodes for x and   *
*             y.  Those nodes were created for a containing                *
*             OpApplNode.                                                  *
*                                                                          *
*    arity : The number of paramters                                       *
*                                                                          *
*    body : An OpApplNode for the expression exp.                          *
*                                                                          *
*    labels : A Hashtable for the labels that appear immediately           *
*             within expression exp.                                       *
***************************************************************************/
package tla2sany.semantic;

import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;

import tla2sany.explorer.ExploreNode;
import tla2sany.parser.SyntaxTreeNode;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.utilities.Vector;
import util.UniqueString;
import util.WrongInvocationException;


public class LabelNode extends ExprNode 
                       implements ExploreNode, OpDefOrLabelNode {

  /*************************************************************************
  * The fields.                                                            *
  *************************************************************************/
  UniqueString name ;
    /***********************************************************************
    * The name of the label                                                *
    ***********************************************************************/
    
  int arity;   
    /***********************************************************************
    * The same as for an OpDefOrDeclNode--the number of arguments to the   *
    * label.                                                               *
    ***********************************************************************/

  FormalParamNode[] params = null;    
    /***********************************************************************
    * The array of formal parameter nodes for this label.  These are all   *
    * FormalParamNode objects that were "declared" as bound symbols in     *
    * OpApplNode objects that are ancestors of this LabelNode in the       *
    * semantic tree.                                                       *
    ***********************************************************************/

  public boolean isAssumeProve = false ;
    /***********************************************************************
    * True iff this node represents a labeled ASSUME/PROVE rather than a   *
    * labeled expression.                                                  *
    ***********************************************************************/
    
  /* ExprNode */ LevelNode body   = null;
    /***********************************************************************
    * The expression being labeled.                                        *
    *                                                                      *
    * Note, for a label imported by instantiation, this.body may actually  *
    * be a semantic node in a different module.  See the comments at the   *
    * beginning of OpDefOrLabelNode.java for an explanation.               *
    ***********************************************************************/

  private Hashtable labels = null ;    
    /***********************************************************************
    * This field is used to implement the OpDefOrLabel interface.  It is   *
    * a hashtable of OpDefNode objects representing labels within the      *
    * body that are not within the scope of an inner label or LET          *
    * definition.                                                          *
    ***********************************************************************/

  ThmOrAssumpDefNode goal = null ;
  int goalClause ;
    /***********************************************************************
    * If the label appears within an ASSUME/PROVE, then goal is the        *
    * named theorem or proof-step node whose body the ASSUME/PROVE is in,  *
    * and goalClause is the number of the clause within which it appears   *
    * (where the PROOF is the last clause).  Otherwise, goal is null.      *
    *                                                                      *
    * Note: If ap is the AssumeProveNode corresponding to the outer        *
    * ASSUME/PROVE containing the label, then goal = ap.goal, even if      *
    * label appears within an inner ASSUME/PROOF.                          *
    ***********************************************************************/

  public SymbolNode subExpressionOf = null ;
    /***********************************************************************
    * For an expression that is constructed as a subexpression of a        *
    * UserDefinedOpNode or ThmOrAssumpDefNode, this field equals that      *
    * node.                                                                *
    ***********************************************************************/

  /*************************************************************************
  * The constructor.                                                       *
  *************************************************************************/
  LabelNode(TreeNode tn,           // the syntax tree node
            UniqueString nm,       // name
            FormalParamNode[] pms, // params
            ThmOrAssumpDefNode gl, // goal
            int  clause,           // goalClause 
            /* ExprNode */ LevelNode    bdy, // body
            boolean isAP           // isAssumeProve value
) {    
    super(LabelKind, tn);
    this.name          = nm;
    this.params        = pms;
    this.arity         = pms.length;
    this.goal          = gl ;
    this.goalClause    = clause ;
    this.body          = bdy;
    this.isAssumeProve = isAP ;
   }

  /*************************************************************************
  * A constructor just used to construct nullLabelNode.                    *
  *************************************************************************/
  LabelNode(LevelNode /* ExprNode */ bdy) {
    super(LabelKind, SyntaxTreeNode.nullSTN);
    this.name   = UniqueString.uniqueStringOf("nullLabelNode");
    this.params = new FormalParamNode[0] ;
    this.arity  = 0 ;
    this.goal   = null ;
    this.body   = bdy;
   }

  
  public UniqueString getName() {return this.name; } 

  /*************************************************************************
  * The following methods implement the OpDefOrLabel interface.            *
  *                                                                        *
  * These are the same as the other classes that implement the interface.  *
  * There doesn't seem to be any easy way to write these methods only      *
  * once.                                                                  *
  *************************************************************************/
  public void setLabels(Hashtable ht) {labels = ht; }
    /***********************************************************************
    * Sets the set of labels.                                              *
    ***********************************************************************/

  public LabelNode getLabel(UniqueString us) {
    /***********************************************************************
    * If the hashtable `labels' contains a LabelNode with name `us',       *
    * then that LabelNode is returned; otherwise null is returned.         *
    ***********************************************************************/
    if (labels == null) {return null;} ;
    return (LabelNode) labels.get(us) ;    
   }

  public boolean addLabel(LabelNode odn) {
    /***********************************************************************
    * If the hashtable `labels' contains no OpDefNode with the same name   *
    * as odn, then odn is added to the set and true is return; else the    *
    * set is unchanged and false is returned.                              *
    ***********************************************************************/
    if (labels == null) {labels = new Hashtable(); } ;
    if (labels.containsKey(odn)) {return false ;} ;
    labels.put(odn.getName(), odn) ;
    return true;
   }
  
  public LabelNode[] getLabels() {
    /***********************************************************************
    * Returns an array containing the Label objects in the hashtable       *
    * `labels'.                                                            *
    ***********************************************************************/
    if (labels == null) {return new LabelNode[0];} ;
    Vector v = new Vector() ;
    Enumeration e = labels.elements() ;
    while (e.hasMoreElements()) { v.addElement(e.nextElement()); } ;
    LabelNode[] retVal = new LabelNode[v.size()] ;
    for (int i = 0 ; i < v.size() ; i++) 
      {retVal[i] = (LabelNode) v.elementAt(i); } ;
    return retVal ;
   }

  public int getArity() {return arity; }   

  public /* ExprNode */ LevelNode getBody() {return body; }

  public SemanticNode getGoal() {return goal; }


  /*************************************************************************
  * Level-Checking.                                                        *
  *************************************************************************/
  public final boolean levelCheck(int iter) {
    if (levelChecked >= iter) {return true ;} ;
    levelChecked = iter;
    boolean retVal = true ;
    for (int i=0; i < params.length; i++) {
      if (params[i] != null) {params[i].levelCheck(iter);} ;
     } ;
    return this.body.levelCheck(iter) && retVal ;
  }

  public final int getLevel() {
    if (levelChecked == 0) 
      {throw new WrongInvocationException("getLevel called for TheoremNode before levelCheck");};
    return this.body.getLevel();
  }

  public final HashSet getLevelParams() {
    if (levelChecked == 0) 
      {throw new WrongInvocationException("getLevelParams called for ThmNode before levelCheck");};
    return this.body.getLevelParams();
  }

  public final HashSet getAllParams() {
    if (levelChecked == 0) 
      {throw new WrongInvocationException("getAllParams called for ThmNode before levelCheck");};
    return this.body.getAllParams();
  }

  public final SetOfLevelConstraints getLevelConstraints() {
    if (levelChecked == 0) 
       {throw new WrongInvocationException("getLevelConstraints called for ThmNode before levelCheck");};
    return this.body.getLevelConstraints();
  }

  public final SetOfArgLevelConstraints getArgLevelConstraints() {
    if (levelChecked == 0) 
      {throw new WrongInvocationException("getArgLevelConstraints called for ThmNode before levelCheck");};
    return this.body.getArgLevelConstraints();
  }

  public final HashSet getArgLevelParams() {
    if (levelChecked == 0) 
      {throw new WrongInvocationException("getArgLevelParams called for ThmNode before levelCheck");};
    return this.body.getArgLevelParams();
  }

  /* 
   * The following method was inexplicably missing until added by LL
   * on 16 October 2013.
   * 
   * @see tla2sany.semantic.SemanticNode#getChildren()
   */
  public SemanticNode[] getChildren() {
      return new SemanticNode[] { this.body };
  }
  /*************************************************************************
  * The methods for implementing the ExploreNode interface.                *
  *************************************************************************/
  public final void walkGraph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);
    if (semNodesTable.get(uid) != null) return;
    semNodesTable.put(new Integer(myUID), this);
    if (body != null) body.walkGraph(semNodesTable);
    for (int i = 0 ; i < params.length; i++) {
      params[i].walkGraph(semNodesTable);
     } ;
  }
  
  public final String toString(int depth) {
    if (depth <= 0) return "";
    String ret = "\n*LabelNode: " + super.toString(depth);
    ret += Strings.indent(2, "\nname: " + name.toString()) ;
    for (int i = 0; i < params.length; i++) {
      ret += Strings.indent(2,
                            "\nparam[" + i + "]:" + 
                                 Strings.indent(2, 
                                                params[i].toString(depth-1)));
     } ;
    ret += Strings.indent(2, "\nisAssumeProve: " + isAssumeProve) ;
    ret += Strings.indent(2, "\nBody:" + 
                               Strings.indent(2, body.toString(depth-1)));

    /***********************************************************************
    * The following is the same for all classes that implement the         *
    * OpDefOrLabelNode interface.                                          *
    ***********************************************************************/
    if (labels != null) {
       ret += "\n  Labels: " ;
       Enumeration list = labels.keys() ;
       while (list.hasMoreElements()) {
          ret += ((UniqueString) list.nextElement()).toString() + "  " ;
         } ;
      } 
    else {ret += "\n  Labels: null";} ;
    if (this.subExpressionOf != null) { 
       ret += Strings.indent(2, "\nsubExpressionOf: " + 
                  Strings.indent(2, this.subExpressionOf.toString(1))) ;} ;

    if (goal != null) {
      ret += "\n goal: " + Strings.indent(4, this.goal.toString(1)) +
             "\n goalClause: " + goalClause ;
     } ;
    return ret;
  }
   
 }
