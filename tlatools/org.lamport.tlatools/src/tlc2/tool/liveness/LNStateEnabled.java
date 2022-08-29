// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:15 PST by lamport
//      modified on Sat Jul 28 00:36:53 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.st.TreeNode;
import tlc2.tool.IActionItemList;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateFun;
import tlc2.util.Context;

/**
 * The Enabled Predicate
 *
 * <p>
 * For any action A, we define <i>Enabled A<i> to be the predicate that is true for a
 * state iff it is possible to take an <i>A<i> step starting in that state.
 * </p>
 *
 * <p>
 * If action <i>A<i> represents an atomic operation of a program, then <i>Enabled A<i> is
 * true for those states in which it is possible to perform the operation.
 * </p>
 */
class LNStateEnabled extends LNState {
    private final ExprNode pred;
    private final ExprNode subscript;
    private final boolean isBox;

    public LNStateEnabled(final ExprNode pred, final Context con, final ExprNode subscript, final boolean isBox) {
        super(con);
        this.pred = pred;
        this.subscript = subscript;
        this.isBox = isBox;
    }

    @Override
    public final boolean eval(final ITool tool, final TLCState s1, final TLCState s2) {
        // Note that s2 is useless.
        if (this.isBox && this.subscript != null) {
            return true;
        }

        TLCState sfun = TLCStateFun.Empty;
        final Context c1 = Context.branch(getContext());
        if (this.subscript != null) {
            sfun = tool.enabled(this.pred, c1, s1, sfun, this.subscript, IActionItemList.CHANGED);
        } else {
            sfun = tool.enabled(this.pred, c1, s1, sfun);
        }
        return sfun != null;
    }

    @Override
    public final void toString(final StringBuilder sb, final String padding) {
        sb.append("ENABLED ");
        if (this.subscript == null) {
            this.pred.toString(sb, padding + "        ");
        } else {
            sb.append((this.isBox) ? "[" : "<");
            this.pred.toString(sb, padding + "         ");
            sb.append((this.isBox) ? "]_" : ">_").append(this.subscript);
        }
    }

    /* (non-Javadoc)
     * @see tlc2.tool.liveness.LiveExprNode#toDotViz()
     */
    @Override
    public String toDotViz() {
        final StringBuilder sb = new StringBuilder();
        if (this.pred instanceof final OpApplNode oan) {
            sb.append("(");
            // Zeros
            final TreeNode[] zero = oan.getTreeNode().zero();
            for (final TreeNode treeNode : zero) {
                // TreeNode is interface with only STN being impl => unchecked
                // cast is safe.
                final SyntaxTreeNode stn = (SyntaxTreeNode) treeNode;
                sb.append(stn.getHumanReadableImage());
            }
            // Ones
            final TreeNode[] one = oan.getTreeNode().one();
            if (one != null) {
                for (final TreeNode treeNode : one) {
                    final SyntaxTreeNode stn = (SyntaxTreeNode) treeNode;
                    sb.append(stn.getHumanReadableImage());
                }
            }
            sb.append(")");
        } else {
            toString(sb, "");
        }
        return sb.toString();
    }

}
