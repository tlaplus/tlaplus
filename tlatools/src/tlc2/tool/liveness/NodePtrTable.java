// Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:46 PST by lamport
//      modified on Sun Jul 29 23:09:54 PDT 2001 by yuanyu

package tlc2.tool.liveness;

public final class NodePtrTable {
  private int count;
  private int length;
  private int thresh;
  private long[] keys;
  private long[] elems;
  private int[][] nodes;

  public NodePtrTable(int size, boolean hasTableau) {
    this.count = 0;
    this.length = size;
    this.thresh = (int)(size * 0.75);
    if (hasTableau) {
      this.keys = null;
      this.elems = null;
      this.nodes = new int[size][];
    }
    else {
      this.keys = new long[size];      
      this.elems = new long[size];
      for (int i = 0; i < size; i++) {
	this.elems[i] = -1;
      }
      this.nodes = null;
    }
  }

  public NodePtrTable(int count, long[] keys, long[] elems, int[][] nodes) {
    this.count = count;
    this.keys = keys;
    this.elems = elems;
    this.nodes = nodes;
    this.length = (keys == null) ? nodes.length : keys.length;
    this.thresh = (int)(this.length * 0.75);
  }

  public final NodePtrTable copy() {
    long[] keys1 = null;
    long[] elems1 = null;
    if (this.keys != null) {
      keys1 = new long[this.length];
      System.arraycopy(this.keys, 0, keys1, 0, this.length);
      elems1 = new long[this.keys.length];
      System.arraycopy(this.elems, 0, elems1, 0, this.length);
    }
    int[][] nodes1 = null;
    if (this.nodes != null) {
      nodes1 = new int[this.length][];
      for (int i = 0; i < this.length; i++) {
	if (this.nodes[i] != null) {
	  nodes1[i] = new int[this.nodes[i].length];
	  System.arraycopy(this.nodes[i], 0, nodes1[i], 0, this.nodes[i].length);
	}
      }
    }
    return new NodePtrTable(this.count, keys1, elems1, nodes1);
  }
  
  /* Double the table when the table is full by the threshhold. */
  private final void grow() {
    this.length = 2*this.length + 1;
    this.thresh = (int)(this.length * 0.75);
    if (this.nodes == null) {
      this.count = 0;
      long[] oldKeys = this.keys;
      long[] oldElems = this.elems;
      this.keys = new long[this.length];
      this.elems = new long[this.length];
      for (int i = 0; i < this.length; i++) {
	this.elems[i] = -1;
      }
      for (int i = 0; i < oldElems.length; i++) {
	long elem = oldElems[i];
	if (elem != -1) this.put(oldKeys[i], elem);
      }
    }
    else {
      int[][] oldNodes = this.nodes;
      this.nodes = new int[this.length][];
      for (int i = 0; i < oldNodes.length; i++) {
	int[] node = oldNodes[i];
	if (node != null) this.put(node);
      }
    }
  }

  private final void put(int[] node) {
    long k = getKey(node);
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      if (this.nodes[loc] == null) {
	this.nodes[loc] = node;
	return;
      }
      loc = (loc + 1) % this.length;
    }
  }
  
  /* The number of elements in this table. */
  public final int size() { return this.count; }

  /**
   * Add <k, elem> into the table. If the table has already
   * contained k, overwrite the old value.
   */
  public final void put(long k, long elem) {
    if (this.count >= this.thresh) this.grow();
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      if (this.elems[loc] == -1) {
	this.keys[loc] = k;
	this.elems[loc] = elem;
	this.count++;
	return;
      }
      if (this.keys[loc] == k) {
	this.elems[loc] = elem;
	return;
      }
      loc = (loc + 1) % this.length;
    }
  }

  /**
   * Add <tidx, elem> into the table. If the table has already
   * contained <k, tidx>, overwrite the old value.
   */
  public final void put(long k, int tidx, long elem) {
    if (this.count >= this.thresh) this.grow();
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      int[] node = this.nodes[loc];
      if (node == null) {
	this.nodes[loc] = addElem(k, tidx, elem);
	this.count++;
	return;
      }
      if (getKey(node) == k) {
	int cloc = getIdx(node, tidx);
	if (cloc == -1) {
	  this.nodes[loc] = addElem(node, tidx, elem);
	  // this.count++;	  
	}
	else {
	  putElem(this.nodes[loc], elem, cloc);
	}
	return;
      }
      loc = (loc + 1) % this.length;
    }
  }

  /* Return the value with key k. Otherwise, return -1. */  
  public final long get(long k) {
    if (count >= thresh) this.grow();
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      if (this.elems[loc] == -1) return -1;
      if (this.keys[loc] == k) return this.elems[loc];
      loc = (loc + 1) % this.length;
    }
  }

  /**
   * Return the value associated with the key <k, tidx> if the table
   * contains <k, tidx>.  Otherwise, return -1.
   */  
  public final long get(long k, int tidx) {
    if (count >= thresh) this.grow();
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      int[] node = this.nodes[loc];
      if (node == null) return -1;
      if (getKey(node) == k) {
	int idx = getIdx(node, tidx);
	if (idx == -1) return -1;
	return getElem(node, idx);
      }
      loc = (loc + 1) % this.length;
    }
  }
  
  /* Return k's location if the table contains k. Otherwise, return -1. */  
  public final int getLoc(long k) {
    if (count >= thresh) this.grow();
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      if (this.elems[loc] == -1) return -1;
      if (this.keys[loc] == k) return loc;
      loc = (loc + 1) % this.length;
    }
  }

  /**
   * Return k's location if the table contains <k, tidx>. Otherwise,
   * return -1.
   */  
  public final int getLoc(long k, int tidx) {
    if (count >= thresh) this.grow();
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      int[] node = this.nodes[loc];
      if (node == null) return -1;
      if (getKey(node) == k) {
	if (getIdx(node, tidx) == -1) return -1;
	return loc;
      }
      loc = (loc + 1) % this.length;
    }
  }

  /* Return all nodes with key k. Return null if this does not contain k. */  
  public final int[] getNodes(long k) {
    if (count >= thresh) this.grow();
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      int[] node = this.nodes[loc];
      if (node == null) return null;
      if (getKey(node) == k) return this.nodes[loc];
      loc = (loc + 1) % this.length;
    }
  }

  /* Return k's location. Return -1 if this does not contain k. */  
  public final int getNodesLoc(long k) {
    if (count >= thresh) this.grow();
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      int[] node = this.nodes[loc];
      if (node == null) return -1;
      if (getKey(node) == k) return loc;
      loc = (loc + 1) % this.length;
    }
  }
  
  public final long getByLoc(int loc) { return this.elems[loc]; }

  public final long getKeyByLoc(int loc) { return this.keys[loc]; }
  
  public final int[] getNodesByLoc(int loc) {
    return this.nodes[loc];
  }

  public final void putByLoc(long k, long elem, int loc) {
    this.keys[loc] = k;
    this.elems[loc] = elem;
  }
  
  public final void putNodesByLoc(int[] node, int loc) {
    this.nodes[loc] = node;
  }
  
  /**
   * This method returns true iff we have already done the nodes with
   * key k.  If we have done with k and a new node is being added, we
   * must get this new node done.
   */
  public final boolean isDone(long k) {
    int[] node = this.getNodes(k);
    if (node == null) return false;
    if (node.length == 2) return true;
    return node[3] != -2;
  }

  public final int setDone(long k) {
    if (this.count >= this.thresh) this.grow();
    int loc = ((int)k & 0x7FFFFFFF) % this.length;
    while (true) {
      int[] node = this.nodes[loc];
      if (node == null) {
	this.nodes[loc] = addKey(k);
	this.count++;
	return loc;
      }
      if (getKey(node) == k) {
	if (node.length > 2 && node[3] == -2) {
	  node[3] = -3;
	}
	return loc;
      }
      loc = (loc + 1) % this.length;
    }
  }    

  public final boolean isGood() {
    if (this.nodes == null) return true;
    for (int i = 0; i < this.nodes.length; i++) {
      int[] node = this.nodes[i];
      if (node != null) {
	for (int j = 3; j < node.length; j += 3) {
	  if (node[j] < 0) return false;
	}
      }
    }
    return true;
  }
  
  public final void resetElems() {
    if (this.nodes == null) {
      for (int i = 0; i < this.keys.length; i++) {
	this.elems[i] &= 0x7FFFFFFFFFFFFFFFL;
      }
    }
    else {
      for (int i = 0; i < this.nodes.length; i++) {
	int[] node = this.nodes[i];
	if (node != null) {
	  for (int j = 3; j < node.length; j += 3) {
	    node[j] &= 0x7FFFFFFF;
	  }
	}
      }
    }
  }
  
  public final int getSize() { return this.length; }

  public static long getKey(int[] node) {
    long high = node[0];
    long low = node[1];
    return (high << 32) | (low & 0xFFFFFFFFL);
  }

  public static int[] addKey(long key) {
    int[] node = new int[2];
    node[0] = (int)(key >>> 32);
    node[1] = (int)(key & 0xFFFFFFFFL);
    return node;
  }
  
  public static int[] addElem(long key, int tidx, long elem) {
    int[] node = new int[5];
    node[0] = (int)(key >>> 32);
    node[1] = (int)(key & 0xFFFFFFFFL);
    node[2] = tidx;
    node[3] = (int)(elem >>> 32);
    node[4] = (int)(elem & 0xFFFFFFFFL);
    return node;
  }

  public static int[] addElem(int[] node, int tidx, long elem) {
    int len = node.length;
    int[] newNode = new int[len+3];
    System.arraycopy(node, 0, newNode, 0, len);
    newNode[len] = tidx;
    newNode[len+1] = (int)(elem >>> 32);
    newNode[len+2] = (int)(elem & 0xFFFFFFFFL);
    return newNode;
  }

  public static int getIdx(int[] node, int tidx) {
    int len = node.length;
    for (int i = 2; i < len; i += 3) {
      if (node[i] == tidx) return i;
    }
    return -1;
  }

  public static long getElem(int[] node, int loc) {
    long high = node[loc+1];
    long low = node[loc+2];
    return (high << 32) | (low & 0xFFFFFFFFL);
  }

  public static void putElem(int[] node, long elem, int loc) {
    node[loc+1] = (int)(elem >>> 32);
    node[loc+2] = (int)(elem & 0xFFFFFFFFL);
  }

  public static int getTidx(int[] node, int loc) {
    return node[loc];
  }

  public static int startLoc(int[] node) {
    return (node.length > 2) ? 2 : -1;
  }

  public static int nextLoc(int[] node, int curLoc) {
    int loc = curLoc + 3;
    return (loc < node.length) ? loc : -1;
  }
  
  public static boolean isSeen(int[] nodes, int tloc) {
    return getElem(nodes, tloc) < 0;
  }
    
  public static void setSeen(int[] nodes, int tloc) {
    long ptr = getElem(nodes, tloc);
    putElem(nodes, (ptr | 0x8000000000000000L), tloc);
  }

  public static long getPtr(long ptr) {
    return (ptr & 0x7FFFFFFFFFFFFFFFL);
  }

  public static boolean isSeen(int[] nodes) {
    return nodes[3] < 0;
  }
    
  public static void setSeen(int[] nodes) {
    nodes[3] |= 0x80000000;
  }

  public static int getParent(int[] nodes) {
    return nodes[4];
  }
  
  public static void setParent(int[] nodes, int loc) {
    nodes[4] = loc;
  }

}
