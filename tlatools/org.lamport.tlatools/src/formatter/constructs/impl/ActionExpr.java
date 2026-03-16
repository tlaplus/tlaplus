package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: `[Next]_vars`
 */
public class ActionExpr implements TlaConstruct {
    @Override
    public String getName() {
        return "N_ActionExpr";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.ACTION_EXPR.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 4);
        return context.buildChild(z[0]) // [
                .append(context.buildChild(z[1])) // GeneralIdentifier
                .append(context.buildChild(z[2])) // ]_
                .append(context.buildChild(z[3])); // GeneralIdentifier
    }
}
