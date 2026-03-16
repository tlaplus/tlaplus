package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: `Head(s)`
 */
public class OpApplicationConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_OpApplication";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.OP_APPLICATION.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 2);
        return context.buildChild(z[0])
                .append(context.buildChild(z[1]));
    }
}
