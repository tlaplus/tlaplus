// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:33:53 PST by lamport
//      modified on Thu Sep 21 15:39:03 PDT 2000 by yuanyu

package tlc2.tool.liveness;

import java.util.ArrayList;

public class TBParVec extends ArrayList<TBPar> {

    private static final long serialVersionUID = -3448802399964070243L;

    public TBParVec(final int size) {
        super(size);
    }

    public final TBPar parAt(final int i) {
        return get(i);
    }

    /* This method tests whether a particle is in a list of other particles */
    public final boolean contains(final TBPar par) {
        for (int i = 0; i < this.size(); i++) {
            if (par.equals(this.parAt(i))) {
                return true;
            }
        }
        return false;
    }

    /* This method unions two lists of particles */
    public final TBParVec union(final TBParVec ps) {
        final TBParVec res = new TBParVec(this.size() + ps.size());
        for (int i = 0; i < this.size(); i++) {
            if (!ps.contains(this.parAt(i))) {
                res.add(this.parAt(i));
            }
        }
        for (int i = 0; i < ps.size(); i++) {
            res.add(ps.parAt(i));
        }
        return res;
    }

    /* The string representation. */
    public final void toString(final StringBuilder sb, final String padding) {
        sb.append("{");
        final String padding1 = padding + " ";
        if (this.size() != 0) {
            this.parAt(0).toString(sb, padding1);
        }
        for (int i = 1; i < this.size(); i++) {
            sb.append(",\n");
            sb.append(padding1);
            this.parAt(i).toString(sb, padding1);
        }
        sb.append("}");
    }

    public final String toString() {
        final StringBuilder sb = new StringBuilder();
        this.toString(sb, "");
        return sb.toString();
    }

}
