// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:31 PST by lamport
//      modified on Wed Dec  5 22:41:28 PST 2001 by yuanyu

package tlc2.tool.liveness;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.util.MemObjectQueue;
import tlc2.util.MemObjectStack;
import tlc2.util.Vect;

public class BEGraph {
  /**
   * BEGraph represents the behaviour graph.
   */
  public Vect initNodes;
  public String metadir;
  public NodeTable allNodes;

  public BEGraph(String metadir, boolean isBT) {
    this.initNodes = new Vect();
    this.metadir = metadir;
    this.allNodes = new NodeTable(127, isBT);
  }    

  /**
   * This method resets the number field of all nodes in this
   * behavior graph to 0.  Assume that all the nodes have
   * non-zero number fields.
   */
  public final void resetNumberField() {
    MemObjectStack stack = new MemObjectStack(this.metadir, "resetstack");
    for (int i = 0; i < this.initNodes.size(); i++) {
      BEGraphNode node = (BEGraphNode)this.initNodes.elementAt(i);
      if (node.resetNumberField() != 0) {
	stack.push(this.initNodes.elementAt(i));
      }
    }
    while (stack.size() != 0) {
      BEGraphNode node = (BEGraphNode)stack.pop();
      for (int i = 0; i < node.nextSize(); i++) {
	BEGraphNode node1 = node.nextAt(i);
	if (node1.resetNumberField() != 0) {
	  stack.push(node1);
	}
      }
    }
  }

  /* Returns the ith initial node. */
  public final BEGraphNode getInitNode(int i) {
    return (BEGraphNode)this.initNodes.elementAt(i);
  }

  public final void addInitNode(BEGraphNode node) {
    this.initNodes.addElement(node);
  }

  /* Returns the number of initial nodes. */
  public final int initSize() { return this.initNodes.size(); }

  /* Returns the shortest path from start to end (inclusive). */
  public static BEGraphNode[] getPath(BEGraphNode start, BEGraphNode end) {
    if (start.equals(end)) {
      start.setParent(null);
    }
    else {
      boolean unseen = start.getVisited();
      MemObjectQueue queue = new MemObjectQueue(null);  // bomb if checkpoint
      start.flipVisited();
      queue.enqueue(new NodeAndParent(start, null));
      boolean found = false;
      while (!found) {
	NodeAndParent np = (NodeAndParent)queue.dequeue();
	if (np == null) {
	  throw new EvalException(EC.TLC_LIVE_BEGRAPH_FAILED_TO_CONSTRUCT);
	}
	BEGraphNode curNode = np.node;
	for (int i = 0; i < curNode.nextSize(); i++) {
	  BEGraphNode nextNode = curNode.nextAt(i);
	  if (nextNode.getVisited() == unseen) {	  
	    if (nextNode.equals(end)) {
	      end.setParent(curNode);
	      found = true;
	      break;
	    }
	    nextNode.flipVisited();
	    queue.enqueue(new NodeAndParent(nextNode, curNode));
	  }
	}
	curNode.setParent(np.parent);
      }
    }
    // Get the path following parent pointers:
    Vect path = new Vect();
    BEGraphNode curNode = end;
    while (curNode != null) {
      path.addElement(curNode);
      curNode = curNode.getParent();
    }
    int sz = path.size();
    BEGraphNode[] bpath = new BEGraphNode[sz];
    for (int i = 0; i < sz; i++) {
      bpath[i] = (BEGraphNode)path.elementAt(sz-i-1);
    }
    return bpath;
  }
  
  /**
   * This method assumes that the visited field of all the nodes is
   * set to the same value.
   */
  public final String toString() {
    StringBuffer buf = new StringBuffer();
    int sz = this.initNodes.size();
    if (sz != 0) {
      boolean seen = this.getInitNode(0).getVisited();
      for (int i = 0; i < this.initNodes.size(); i++) {
	BEGraphNode node = this.getInitNode(i);
	node.toString(buf, seen);
      }
    }
    return buf.toString();
  }

  static class NodeAndParent {
    BEGraphNode node;
    BEGraphNode parent;
    
    NodeAndParent(BEGraphNode node, BEGraphNode parent) {
      this.node = node;
      this.parent = parent;
    }
  }
}
