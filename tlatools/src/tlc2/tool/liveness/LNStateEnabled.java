// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:15 PST by lamport
//      modified on Sat Jul 28 00:36:53 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.st.TreeNode;
import tlc2.tool.ActionItemList;
import tlc2.tool.TLCState;
import tlc2.tool.TLCStateFun;
import tlc2.tool.Tool;
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
 * 
 */
class LNStateEnabled extends LNState {
	private final ExprNode pred;
	private final ExprNode subscript;
	private final boolean isBox;

	public LNStateEnabled(ExprNode pred, Context con, ExprNode subscript, boolean isBox) {
		super(con);
		this.pred = pred;
		this.subscript = subscript;
		this.isBox = isBox;
	}

	public final boolean eval(Tool tool, TLCState s1, TLCState s2) {
		// Note that s2 is useless.
		if (this.isBox && this.subscript != null) {
			return true;
		}

		ActionItemList acts = ActionItemList.Empty;
		TLCState sfun = TLCStateFun.Empty;
		Context c1 = Context.branch(getContext());
		if (this.subscript != null) {
			acts = acts.cons(this.subscript, c1, -3);
		}
		sfun = tool.enabled(this.pred, acts, c1, s1, sfun);
		return sfun != null;
	}

	public final void toString(StringBuffer sb, String padding) {
		sb.append("ENABLED ");
		if (this.subscript == null) {
			this.pred.toString(sb, padding + "        ");
		} else {
			sb.append((this.isBox) ? "[" : "<");
			this.pred.toString(sb, padding + "         ");
			sb.append(((this.isBox) ? "]_" : ">_") + this.subscript);
		}
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.LiveExprNode#toDotViz()
	 */
	public String toDotViz() {
		final StringBuffer sb = new StringBuffer();
		if (this.pred instanceof OpApplNode) {
			final OpApplNode oan = (OpApplNode) this.pred;
			sb.append("(");
			// Zeros
			final TreeNode[] zero = oan.getTreeNode().zero();
			for (TreeNode treeNode : zero) {
				// TreeNode is interface with only STN being impl => unchecked
				// cast is safe.
				SyntaxTreeNode stn = (SyntaxTreeNode) treeNode;
				sb.append(stn.getHumanReadableImage());
			}
			// Ones
			final TreeNode[] one = oan.getTreeNode().one();
			if (one != null) {
				for (TreeNode treeNode : one) {
					SyntaxTreeNode stn = (SyntaxTreeNode) treeNode;
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
