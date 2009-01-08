// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:49 PST by lamport
//      modified on Sun Jul 29 23:09:54 PDT 2001 by yuanyu

package tlc2.tool.liveness;

public final class NodeTable {
  private int count;
  private int length;
  private int thresh;
  private Object[] elems;
  private boolean isBT;

  public NodeTable(int size, boolean isBT) {
    this.count = 0;
    this.length = size;
    this.thresh = size / 2;
    this.elems = new Object[size];
    this.isBT = isBT;
  }

  /* Double the table when the table is full by the threshhold. */
  private final void grow() {
    Object[] oldElems = this.elems;
    this.count = 0;
    this.length = 2 * this.length + 1;
    this.thresh = this.length / 2;
    this.elems = new Object[this.length];
    for (int i = 0; i < oldElems.length; i++) {
      Object elem = oldElems[i];
      if (elem != null) {
	if (this.isBT) {
	  this.putBTNodes(elem);
	}
	else {
	  this.putBENode((BEGraphNode)elem);
	}
      }
    }
  }

  public final int size() { return this.count; }

  public final int putBENode(BEGraphNode node) {
    if (count >= thresh) this.grow();
    long k = node.stateFP;
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      BEGraphNode node1 = (BEGraphNode)this.elems[loc];
      if (node1 == null) {
	this.elems[loc] = node;
	this.count++;
	return loc;
      }
      else if (node1.stateFP == k) {
	this.elems[loc] = node;
	return loc;
      }
      loc = (loc + 1) % this.length;
    }
  }

  public final BEGraphNode getBENode(long k) {
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      BEGraphNode node = (BEGraphNode)this.elems[loc];
      if (node == null) return null;
      if (node.stateFP == k) return node;
      loc = (loc + 1) % this.length;
    }
  }

  private final int putBTNodes(Object nodes) {
    long k = ((nodes instanceof BTGraphNode) ?
	      ((BTGraphNode)nodes).stateFP : ((BTGraphNode[])nodes)[0].stateFP);
    int loc = ((int)k & 0x7FFFFFFF) % this.length;    
    while (this.elems[loc] != null) {
      loc = (loc + 1) % this.length;
    }
    this.elems[loc] = nodes;
    this.count++;
    return loc;
  }
  
  public final int putBTNode(BTGraphNode node) {
    if (this.count >= this.thresh) this.grow();
    long k1 = node.stateFP;
    int k2 = node.getIndex();
    int loc = ((int)k1 & 0x7FFFFFFF) % this.length;
    while (true) {
      Object elem = this.elems[loc];
      if (elem == null) {
	this.elems[loc] = node;
	this.count++;
	return loc;
      }
      else if (elem instanceof BTGraphNode) {
	BTGraphNode btnode = (BTGraphNode)elem;
	if (btnode.stateFP == k1) {
	  if (btnode.isDummy()) {
	    this.elems[loc] = node;
	    // this.count++;
	  }
	  else if (btnode.getIndex() != k2) {
	    BTGraphNode[] newElem = new BTGraphNode[2];
	    newElem[0] = btnode;
	    newElem[1] = node;
	    this.elems[loc] = newElem;
	    // this.count++;
	  }
	  return loc;
	}
      }
      else {
	BTGraphNode[] nodes = (BTGraphNode[])elem;
	if (nodes[0].stateFP == k1) {
	  for (int i = 0; i < nodes.length; i++) {
	    if (nodes[i].getIndex() == k2) return loc;
	  }
	  BTGraphNode[] newElem = new BTGraphNode[nodes.length+1];
	  for (int i = 0; i < nodes.length; i++) {
	    newElem[i] = nodes[i];
	  }
	  newElem[nodes.length] = node;
	  this.elems[loc] = newElem;
	  // this.count++;
	  return loc;
	}
      }
      loc = (loc + 1) % this.length;
    }
  }

  /* This method gets all the nodes with state fingerprint k. */
  public final BTGraphNode[] getBTNode(long k) {
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      Object elem = this.elems[loc];
      if (elem == null) return null;
      if (elem instanceof BTGraphNode) {
	BTGraphNode btnode = (BTGraphNode)elem;
	if (btnode.stateFP == k) {
	  if (btnode.isDummy()) return null;
	  BTGraphNode[] nodes = new BTGraphNode[1];
	  nodes[0] = btnode;
	  return nodes;
	}
      }
      else {
	BTGraphNode[] nodes = (BTGraphNode[])elem;
	if (nodes[0].stateFP == k) return nodes;
      }
      loc = (loc + 1) % this.length;
    }
  }

  public final BTGraphNode[] getBTNodeWithHint(long k, int hintLoc) {
    Object elem = this.elems[hintLoc];
    if (elem != null) {
      if (elem instanceof BTGraphNode) {
	BTGraphNode btnode = (BTGraphNode)elem;
	if (btnode.stateFP == k) {
	  if (btnode.isDummy()) return null;
	  BTGraphNode[] nodes = new BTGraphNode[1];
	  nodes[0] = btnode;
	  return nodes;
	}
      }
      else {
	BTGraphNode[] nodes = (BTGraphNode[])elem;
	if (nodes[0].stateFP == k) return nodes;
      }
    }
    return getBTNode(k);
  }
  
  /**
   * This method gets the node with state fingerprint k1 and tableau
   * node index k2.  It returns null if there is no such node.
   */
  public final BTGraphNode getBTNode(long k1, int k2) {
    int loc = ((int)k1 & 0x7FFFFFFF) % this.length;
    while (true) {
      Object elem = this.elems[loc];
      if (elem == null) return null;
      if (elem instanceof BTGraphNode) {
	BTGraphNode node = (BTGraphNode)elem;
	if (node.stateFP == k1) {
	  if (node.isDummy() || node.getIndex() != k2) {
	    return null;
	  }
	  return node;
	}
      }
      else {
	BTGraphNode[] nodes = (BTGraphNode[])elem;
	if (nodes[0].stateFP == k1) {
	  for (int i = 0; i < nodes.length; i++) {
	    BTGraphNode node = nodes[i];
	    if (node.getIndex() == k2) {
	      return node;
	    }
	  }
	  return null;
	}
      }
      loc = (loc + 1) % this.length;
    }
  }

  /**
   * This method returns true iff we have already done the nodes in
   * elems[idx]. So, if there is a new node being added to elems[idx],
   * we must get this new node done.
   */
  public final boolean isDone(int loc) {
    Object elem = this.elems[loc];
    if (elem == null) return false;
    if (elem instanceof BTGraphNode) {
      return ((BTGraphNode)elem).isDone();
    }
    return ((BTGraphNode[])elem)[0].isDone();
  }

  public final void setDone(long k) {
    if (this.count >= this.thresh) this.grow();
    if (!this.isBT) return;
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      Object elem = this.elems[loc];
      if (elem == null) {
	this.elems[loc] = BTGraphNode.makeDummy(k);
	this.count++;
	return;
      }
      if (elem instanceof BTGraphNode) {
	BTGraphNode node = (BTGraphNode)elem;
	if (node.stateFP == k) {
	  node.setDone();
	  return;
	}
      }
      else {
	BTGraphNode[] nodes = (BTGraphNode[])elem;
	if (nodes[0].stateFP == k) {
	  ((BTGraphNode[])elem)[0].setDone();
	  return;
	}
      }
      loc = (loc + 1) % this.length;
    }
  }    
  
}
