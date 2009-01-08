// Copyright (c) 2007 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import tla2sany.st.TreeNode;

/***************************************************************************
* This abstract class represents a proof.  It just provides a way of       *
* giving a single superclass name to the two classes that extend it:       *
* LeafProofNode and NonLeafProofNode.                                      *
***************************************************************************/
public abstract class ProofNode extends LevelNode {
  ProofNode(int kind, TreeNode stn) { super(kind, stn); }

}
