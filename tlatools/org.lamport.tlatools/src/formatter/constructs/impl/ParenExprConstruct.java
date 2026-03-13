package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Construct implementation for parenthesized expressions.
 * Handles formatting of expressions wrapped in parentheses.
 */
public class ParenExprConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "PAREN_EXPR";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.PAREN_EXPR.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        assert (node.zero() != null && node.zero().length >= 3);
        Doc innerExpr = context.buildChild(node.zero()[1]);
        return Doc.group(context.buildChild(node.zero()[0]) // (
                .appendSpace(innerExpr.indent("( ".length()))
                .appendLineOrSpace(context.buildChild(node.zero()[node.zero().length - 1]))); // )
    }
}