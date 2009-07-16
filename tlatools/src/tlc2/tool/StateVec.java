// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:57 PST by lamport
//      modified on Fri Mar  2 15:37:34 PST 2001 by yuanyu

package tlc2.tool;

import tla2sany.semantic.SemanticNode;
import tlc2.TLCGlobals;
import tlc2.output.EC;
import tlc2.value.Value;
import util.Assert;
import util.UniqueString;

/*
 * This class represents a TLA+ state vector.
 * This is the mutable version, which means that in-place
 * updates are used for improved performance and reduced
 * allocation.
 */
public final class StateVec {
  private TLCState v[];
  private int size;

  private static final TLCState[] emptyStateArr = new TLCState[0];

  public StateVec(TLCState item0) {
    this.size = 1;
    this.v = new TLCState[1];
    this.v[0] = item0;
  }

  public StateVec(int length) {
    this.size = 0;
    if (length == 0) {
      this.v = emptyStateArr;
    }
    else {
      this.v = new TLCState[length];
    }
  }

  private StateVec(TLCState v[]) {
    this.v = v;
    this.size = v.length;
  }

  public final boolean empty() { return (this.size == 0); }

  public final int size() { return this.size; }

  public final void grow(int add) {
    int oldLen = this.v.length;
    if (oldLen >= TLCGlobals.setBound) {
      Assert.fail(EC.TLC_TOO_MNY_POSSIBLE_STATES);
    }
    int newLen = Math.min(Math.max(oldLen+add, 2*oldLen), TLCGlobals.setBound);
    TLCState oldv[] = this.v;
    this.v = new TLCState[newLen];
    for (int i = 0; i < this.size; i++) {
      this.v[i] = oldv[i];
    }
  }

  public final TLCState elementAt(int i) { return this.v[i]; }

  public final void clear() {
    this.size = 0;
  }
  
  // Add the binding to all the variables
  public final StateVec bind(UniqueString var, Value val, SemanticNode ast) {
    for (int i = 0; i < this.size; i++) {
      TLCState s = this.v[i];
      if (s.containsKey(var)) return null;
      v[i] = s.bind(var, val, ast);
    }
    return this;
  }

  // Bind a value in one of the states.
  public final StateVec bindAt(int i, UniqueString var, Value val, SemanticNode ast) {
    v[i] = v[i].bind(var, val, ast);
    return this;
  }

  public final StateVec addElement(TLCState state) {
    if (this.size >= this.v.length) { grow(1); }
    this.v[this.size++] = state;
    return this;
  }
  
  public final StateVec addElements(StateVec s1) {
    StateVec s0 = this;

    if (s1.size > s0.size) {
      StateVec tmp = s0;
      s0 = s1;
      s1 = tmp;
    }

    int size0 = s0.size;
    int size1 = s1.size;
    TLCState[] v0 = s0.v;
    TLCState[] v1 = s1.v;
    if (v0.length < size0 + size1) {
      s0.grow(size1);
      v0 = s0.v;
    }
    for (int i = 0; i < size1; i++) {
      v0[size0+i] = v1[i];
    }
    s0.size = size0 + size1;
    return s0;
  }

  public final void removeElement(int index) {
    this.v[index] = this.v[this.size-1];
    this.size--;
  }
  
  public final StateVec copy() {
    TLCState[] res = new TLCState[this.size];
    for (int i = 0; i < this.size; i++) {
      res[i] = this.v[i].copy();
    }
    return new StateVec(res);
  }

  // Really really deep copy
  public final StateVec deepCopy() {
    TLCState[] res = new TLCState[this.size];
    for (int i = 0; i < this.size; i++) {
      res[i] = this.v[i].deepCopy();
    }
    return new StateVec(res);
  }

  public final void reset() { this.size = 0; }
  
  public final void deepNormalize() {
    for (int i = 0; i < this.size; i++) {
      this.v[i].deepNormalize();
    }
  }

  public final String toString() {
    StringBuffer sb = new StringBuffer();
    sb.append("{");
    if (this.size > 0) {
      sb.append(this.v[0].toString());
    }
    for (int i = 1; i < this.size; i++) {
      sb.append(", ");
      sb.append(this.v[i].toString());
    }
    sb.append("}");
    return sb.toString();
  }

}
