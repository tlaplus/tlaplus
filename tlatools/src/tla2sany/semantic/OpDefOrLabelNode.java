// Last modified on Sat 28 Apr 2007 at 14:37:16 PST by lamport

/***************************************************************************
* This interface is implemented by LabelNode, OpDefNode, and               *
* ThmOrAssumpDefNode.  It contains methods for accessing the set of        *
* LabelNode objects for labels that occur immediately within this          *
* node--that is, with no intervening LabelNode or OpDefNode in the         *
* semantic tree.  This set is represented by a Hashtable, and by the null  *
* object if the set is empty.  The Hashtable key of a LabelNode ln is      *
* ln.getName(), which is a UniqueString.                                   *
*                                                                          *
* WARNING: If an OpDefNode odn represents an operator obtained by          *
* instanting a module M, then each LabelNode object lab returned by        *
* getLabel() and getLabels() is the same one as in the OpDefNode           *
* from module M. Therefore, lab.body is an expression in module M, not in  *
* the current module.  The meaning of this label must be interpreted as    *
* lab.body under the substitutions of the instantiation.  This             *
* substitution is described by the SubstInNode odn.body.  Hence, to        *
* interpret a label in the label set of an OpDefNode odn, one must check   *
* if odn.body is a SubstInNode, in which case that substitution must be    *
* applied to the body of the label.  In general, odn is the result of a    *
* series of k instantiations iff odn.body.body. ... .body is a SubstIn     *
* node, for up to k ".body"s.                                              *
*                                                                          *
* A similar warning applies to ThmOrAssumpDefNode objects, except they     *
* use APSubstInNode objects instead of SubstInNode objects for the         *
* instantiation.                                                           *
***************************************************************************/

package tla2sany.semantic;

import java.util.Hashtable;

import util.UniqueString;

interface OpDefOrLabelNode {

public abstract void setLabels(Hashtable ht) ;
  /*************************************************************************
  * Set the set of labels to ht.                                           *
  *************************************************************************/
  
public abstract LabelNode getLabel(UniqueString us) ;
  /*************************************************************************
  * If the set contains an OpDefNode with name `us', then that OpDefNode   *
  * is returned; otherwise null is returned.                               *
  *************************************************************************/

public abstract boolean addLabel(LabelNode odn) ;
  /*************************************************************************
  * If the set contains no LabelNode with the same name as odn, then odn   *
  * is added to the set and true is return; else the set is unchanged and  *
  * false is returned.                                                     *
  *************************************************************************/
  
public abstract LabelNode[] getLabels() ;
  /*************************************************************************
  * Returns an array containing the Label objects in the set.              *
  *************************************************************************/
  
public abstract int getArity();
  /*************************************************************************
  * Returns the arity of the label or operator.                            *
  *************************************************************************/
  
}