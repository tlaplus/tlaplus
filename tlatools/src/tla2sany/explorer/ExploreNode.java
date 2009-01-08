// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.explorer;
import java.util.Hashtable;

/**
 * implemented by the following classes (as well as various abstract and  superclasses):
 *
 *        AssumeNode, AtNode, Context, DecimalNode, FormalParamNode, LetInNode, NumeralNode, 
 *        OpApplNode, OpArgNode, OpDeclNode, OpDefNode, StringNode, Subst, SubstInNode, TheoremNode
 */

public interface ExploreNode {

  public String toString(int depth);
    /***********************************************************************
    * This displays the node as a string.  Apparently, the string should   *
    * begin with "\n" to start a new line.  The depth parameter is         *
    * apparently used to control the limit on the depth being displayed.   *
    * Apparently, the method should return "" if depth <= 0, and I         *
    * imagine it should call foo.toString(depth-1) to print each           *
    * descendant foo.                                                      *
    ***********************************************************************/
  public String levelDataToString();
  public void   walkGraph(Hashtable semNodesTable);
    /***********************************************************************
    * This method is apparently supposed to insert an entry in             *
    * semNodesTable for itself and every descendant in the semantic tree   *
    * by executing                                                         *
    *                                                                      *
    *     Integer uid = new Integer(myUID);                                *
    *     if (semNodesTable.get(uid) != null) return;                      *
    *     semNodesTable.put(uid, this);                                    *
    *                                                                      *
    * and then calling child.walkGraph(semNodesTable) for every            *
    * descendant.                                                          *
    ***********************************************************************/
    
}
