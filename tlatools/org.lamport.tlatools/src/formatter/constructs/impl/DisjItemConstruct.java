package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

public class DisjItemConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_DisjItem";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.DISJ_ITEM.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 2);
        var symbol = context.buildChild(z[0]);
        var expr = context.buildChild(z[1]).indent("/\\ ".length());
        return symbol.appendSpace(expr);
    }
}
