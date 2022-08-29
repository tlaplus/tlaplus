// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.

package tla2sany.semantic;

class ArgLevelParam {
    /*************************************************************************
     * ArgLevelParam objects are used only to implement the elements of the   *
     * set of that name in the specification LevelSpec.tla of level           *
     * checking.  If the ArgLevelParam object alp is in the HashSet of        *
     * objects returned by getArgLevelParams for an expression, then the      *
     * operator alp.op appears somewhere in the expression as a               *
     * subexpression alp.op(...)  in which the alp.i-th argument's level      *
     * depends on the parameter alp.param of the current context.             *
     *************************************************************************/
    final SymbolNode op;
    final int i;
    final SymbolNode param;

    /* Creates new ArgLevelParam */
    public ArgLevelParam(final SymbolNode op, final int i, final SymbolNode param) {
        this.op = op;
        this.i = i;
        this.param = param;
    }

    public final boolean occur(final SymbolNode[] symbols) {
        for (final SymbolNode symbol : symbols) {
            if (this.op == symbol ||
                    this.param == symbol) {
                return true;
            }
        }
        return false;
    }

    public final boolean equals(final Object obj) {
        if (obj instanceof final ArgLevelParam alp) {
            return ((this.op == alp.op) &&
                    (this.i == alp.i) &&
                    (this.param == alp.param));
        }
        return false;
    }

    public final int hashCode() {
        return this.op.hashCode() + this.i + this.param.hashCode();
    }

    public final String toString() {
        return "<" + this.op + ", " + this.i + ", " + this.param + ">";
    }

}
