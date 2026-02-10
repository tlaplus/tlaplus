// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed  4 Jul 2007 at 17:31:51 PST by lamport
//      modified on Wed Jul 25 11:04:30 PDT 2001 by yuanyu

package tlc2.value.impl;

import tla2sany.semantic.FormalParamNode;

/**
 * Represents a single EXCEPT clause in a TLA+ expression of the form
 * {@code [f EXCEPT ![a][b] = v]}. The {@link #path} holds the sequence of
 * subscript arguments ({@code a, b}) and {@link #value} holds the replacement
 * value ({@code v}). The mutable {@link #idx} field tracks how far along the
 * path the EXCEPT has been applied: {@code Value.takeExcept} implementations
 * advance {@code idx} as they descend through nested function/record
 * structures.
 */
public class ValueExcept {
  /** The subscript arguments of the EXCEPT clause, e.g. {@code [a, b]} for {@code ![a][b]}. */
  public Value[] path;
  /** The replacement value, i.e. the right-hand side of the {@code = v} in the EXCEPT clause. */
  public Value value;
  /**
   * Current position in {@link #path}. Advanced by {@code Value.takeExcept}
   * as each level of the path is consumed. When {@code idx >= path.length},
   * the path is fully consumed and {@link #value} should be used.
   */
  public int idx;

  public ValueExcept(Value [] lhs, Value  rhs) {
    this.path = lhs;
    this.value = rhs;
    this.idx = 0;
  }
  
  /**
   * Creates a shallow copy of {@code ex} with {@code idx} set to the given
   * value. Use this to obtain a fresh cursor (idx) into the same path/value pair
   * without mutating the original.
   */
  public ValueExcept(ValueExcept ex, int idx) {
    this.path = ex.path;
    this.value = ex.value;
    this.idx = idx;
  }

  public final ValueExcept checkArg(FcnLambdaValue fcn) {
    Value  argv = this.path[idx];
    if (fcn.getParams().length() == 1) {
      if (!fcn.getParams().domains[0].member(argv)) return null;
    }
    else {
      TupleValue tval = (TupleValue)argv;
      Value [] argList = tval.elems;
      FormalParamNode[][] formals = fcn.getParams().formals;
      Value [] domains = fcn.getParams().domains;
      int argn = 0;
      for (int i = 0; i < fcn.getParams().formals.length; i++) {
        FormalParamNode[] formal = formals[i];
        for (int j = 0; j < formal.length; j++) {
          if (!domains[i].member(argList[argn++])) return null;
        }
      }
    }
    return this;
  }

  public final Value  current() { return this.path[this.idx]; }

  public final boolean isLast() {
    return this.idx == (this.path.length - 1);
  }

  public final String toString() {
    StringBuffer sb = new StringBuffer();
    for (int i = 0; i < path.length; i++) {
      sb.append(".(" + this.idx + ")");
      sb.append(path[i]);
    }
    sb.append(" = ");
    sb.append(this.value);
    return sb.toString();
  }
  
}
