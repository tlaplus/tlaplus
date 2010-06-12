// Portions Copyright (c) 2007 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.Hashtable;

import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import util.UniqueString;

/***************************************************************************
* This class represents definition step of a proof, which consists of a    *
* sequence of operator-, function-, or module-definition steps.  (A        *
* module definition is something like "Id == INSTANCE...".)                *
***************************************************************************/

public class DefStepNode extends LevelNode {

  /*************************************************************************
  * The fields.                                                            *
  *************************************************************************/
  private UniqueString stepNumber ;
    /***********************************************************************
    * The step number of the step if it has one, otherwise null if it's    *
    * not a numbered step.                                                 *
    ***********************************************************************/

  private OpDefNode[] defs ;    
    /***********************************************************************
    * The sequence of definitions.                                         *
    ***********************************************************************/

  /*************************************************************************
  * The constructor.                                                       *
  *************************************************************************/
  public DefStepNode(TreeNode stn, UniqueString stepNum, OpDefNode[] theDefs){
    super(DefStepKind, stn);
    this.stepNumber = stepNum; 
    this.defs = theDefs;
   }
    
  /*************************************************************************
  * The methods just return the field values.                              *
  *************************************************************************/
  public UniqueString getStepNumber() {return stepNumber ;}
  public OpDefNode[] getDefs() {return defs;}   

  public boolean levelCheck(int iter) { 
    /***********************************************************************
    * Level check the steps and the instantiated modules coming from       *
    * module definitions.                                                  *
    ***********************************************************************/
    return this.levelCheckSubnodes(iter, defs) ;
   }

  public void walkGraph(Hashtable semNodesTable) {
    Integer uid = new Integer(myUID);
    if (semNodesTable.get(uid) != null) return;
    semNodesTable.put(new Integer(myUID), this);
    for (int  i = 0; i < defs.length; i++) {
      defs[i].walkGraph(semNodesTable);
      } ;
   }

  public SemanticNode[] getChildren() {
      SemanticNode[] res = new SemanticNode[defs.length];
      for (int i = 0; i < defs.length; i++) {
          res[i] = defs[i];
      }
      return res;
   }
  public String toString(int depth) {
    if (depth <= 0) return "";
    String ret = "\n*DefStepNode:\n"
                  + super.toString(depth)
                  + Strings.indent(2, "\ndefs:") ;
    for (int i = 0 ; i < this.defs.length; i++) {
        ret += Strings.indent(4, this.defs[i].toString(depth-1)) ;
      } ;
    return ret;
   }

}