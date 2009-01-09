// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed  4 Jul 2007 at 17:31:51 PST by lamport
//      modified on Wed Jul 25 11:04:30 PDT 2001 by yuanyu

package tlc2.value;

import tla2sany.semantic.FormalParamNode;

public class ValueExcept {
  public Value[] path;
  public Value value;
  public int idx;

  public ValueExcept(Value[] lhs, Value rhs) {
    this.path = lhs;
    this.value = rhs;
    this.idx = 0;
  }
  
  public ValueExcept(ValueExcept ex, int idx) {
    this.path = ex.path;
    this.value = ex.value;
    this.idx = idx;
  }

  public final ValueExcept checkArg(FcnLambdaValue fcn) {
    Value argv = this.path[idx];
    if (fcn.params.length() == 1) {
      if (!fcn.params.domains[0].member(argv)) return null;
    }
    else {
      TupleValue tval = (TupleValue)argv;
      Value[] argList = tval.elems;
      FormalParamNode[][] formals = fcn.params.formals;
      Value[] domains = fcn.params.domains;
      int argn = 0;
      for (int i = 0; i < fcn.params.formals.length; i++) {
        FormalParamNode[] formal = formals[i];
        for (int j = 0; j < formal.length; j++) {
          if (!domains[i].member(argList[argn++])) return null;
        }
      }
    }
    return this;
  }

  public final Value current() { return this.path[this.idx]; }

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
