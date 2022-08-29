// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed  4 Jul 2007 at 17:31:51 PST by lamport
//      modified on Wed Jul 25 11:04:30 PDT 2001 by yuanyu

package tlc2.value.impl;

import tla2sany.semantic.FormalParamNode;

public class ValueExcept {
    public final Value[] path;
    public final Value value;
    public int idx;

    public ValueExcept(final Value[] lhs, final Value rhs) {
        this.path = lhs;
        this.value = rhs;
        this.idx = 0;
    }

    public ValueExcept(final ValueExcept ex, final int idx) {
        this.path = ex.path;
        this.value = ex.value;
        this.idx = idx;
    }

    public final ValueExcept checkArg(final FcnLambdaValue fcn) {
        final Value argv = this.path[idx];
        if (fcn.getParams().length() == 1) {
            if (!fcn.getParams().domains[0].member(argv)) return null;
        } else {
            final TupleValue tval = (TupleValue) argv;
            final Value[] argList = tval.elems;
            final FormalParamNode[][] formals = fcn.getParams().formals;
            final Value[] domains = fcn.getParams().domains;
            int argn = 0;
            for (int i = 0; i < fcn.getParams().formals.length; i++) {
                final FormalParamNode[] formal = formals[i];
                for (int j = 0; j < formal.length; j++) {
                    if (!domains[i].member(argList[argn++])) return null;
                }
            }
        }
        return this;
    }

    public final Value current() {
        return this.path[this.idx];
    }

    public final boolean isLast() {
        return this.idx == (this.path.length - 1);
    }

    public final String toString() {
        final StringBuilder sb = new StringBuilder();
        for (final Value item : path) {
            sb.append(".(").append(this.idx).append(")");
            sb.append(item);
        }
        sb.append(" = ");
        sb.append(this.value);
        return sb.toString();
    }

}
