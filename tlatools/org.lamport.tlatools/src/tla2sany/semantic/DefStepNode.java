// Portions Copyright (c) 2007 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.Hashtable;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import tla2sany.xml.SymbolContext;
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

  @Override
  public boolean levelCheck(int iter) {
    /***********************************************************************
    * Level check the steps and the instantiated modules coming from       *
    * module definitions.                                                  *
    ***********************************************************************/
    return this.levelCheckSubnodes(iter, defs) ;
   }

  @Override
  public void walkGraph(Hashtable<Integer, ExploreNode> semNodesTable, ExplorerVisitor visitor) {
    Integer uid = Integer.valueOf(myUID);
    if (semNodesTable.get(uid) != null) return;
    semNodesTable.put(uid, this);
    visitor.preVisit(this);
    for (int  i = 0; i < defs.length; i++) {
      defs[i].walkGraph(semNodesTable, visitor);
      } ;
      visitor.postVisit(this);
   }

  @Override
  public SemanticNode[] getChildren() {
      SemanticNode[] res = new SemanticNode[defs.length];
      for (int i = 0; i < defs.length; i++) {
          res[i] = defs[i];
      }
      return res;
   }
  
  @Override
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

  @Override
  protected Element getLevelElement(Document doc, SymbolContext context) {
      Element e = doc.createElement("DefStepNode");
      for (int i=0; i<defs.length;i++) {
        e.appendChild(defs[i].export(doc,context));
      }
      return e;
    }
}
