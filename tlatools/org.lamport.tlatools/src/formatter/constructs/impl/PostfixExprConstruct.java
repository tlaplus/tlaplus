package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: `x'`. the prime operator is GenPostfixOp.
 */
public class PostfixExprConstruct implements TlaConstruct {
    @Override
    public int getSupportedNodeKind() {
        return NodeKind.POSTFIX_EXPR.getId();
    }

    @Override
    public String getName() {
        return "N_PostfixExpr";
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 2);
        var expr = context.buildChild(node.zero()[0]);
        var op = context.buildChild(node.zero()[1]);
        return Doc.group(expr.append(op));

    }
}
