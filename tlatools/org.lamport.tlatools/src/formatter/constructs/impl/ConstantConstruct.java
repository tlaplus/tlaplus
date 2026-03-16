package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * This is the actual "CONSTANT" or "CONSTANTS" keyword in the spec.
 * it has a single child which is the actual CONSTANT keyword along with comments.
 */
public class ConstantConstruct implements TlaConstruct {
    @Override
    public int getSupportedNodeKind() {
        return NodeKind.CONSTANTS.getId();
    }

    @Override
    public String getName() {
        return "N_ConsDecl";
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 1);
        return context.buildChild(z[0]);
    }
}
