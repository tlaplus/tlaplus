// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:30:15 PST by lamport
//      modified on Sat Jul 28 00:37:08 PDT 2001 by yuanyu

package tlc2.tool.liveness;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.st.TreeNode;
import tlc2.output.EC;
import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.Context;
import tlc2.value.BoolValue;
import tlc2.value.Value;
import util.Assert;

/**
 * Handles states
 *
 * @author Leslie Lamport, Yuan Yu, Simon Zambrovski
 * @version $Id$
 */
class LNStateAST extends LNState {
	private final ExprNode body;

	public LNStateAST(ExprNode body, Context con) {
		super(con);
		this.body = body;
	}

	public final ExprNode getBody() {
		return this.body;
	}

	public final boolean eval(Tool tool, TLCState s1, TLCState s2) {
		Value val = tool.eval(this.body, getContext(), s1);
		if (!(val instanceof BoolValue)) {
			Assert.fail(EC.TLC_LIVE_STATE_PREDICATE_NON_BOOL);
		}
		return ((BoolValue) val).val;
	}

	public final void toString(StringBuffer sb, String padding) {
		sb.append(this.body);
	}
	
	/* (non-Javadoc)
	 * @see tlc2.tool.liveness.LiveExprNode#toDotViz()
	 */
	public String toDotViz() {
		final StringBuffer sb = new StringBuffer();
		if (this.body instanceof OpApplNode) {
			final OpApplNode oan = (OpApplNode) this.body;
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
