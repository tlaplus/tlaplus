package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: `-1`.
 * Example: `DOMAIN f`
 * Example: `SUBSET DOMAIN f`
 */
public class PrefixExprConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_PrefixExpr";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.PREFIX_EXPR.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        var genInfixOp = context.buildChild(z[0]);
        var val = context.buildChild(z[1]);
        if (Character.isLetter(z[0].getHumanReadableImage().charAt(0))) {
            // e.g., DOMAIN, SUBSET etc.
            return genInfixOp.appendSpace(val);
        }
        return genInfixOp.append(val);
    }
}
