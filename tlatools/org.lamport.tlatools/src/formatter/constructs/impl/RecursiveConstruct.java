package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

public class RecursiveConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_Recursive";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.RECURSIVE.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        var recursiveKey = context.buildChild(z[0]);
        // TODO: not sure if the for loop is needed.
        for (int i = 1; i < z.length; i++) {
            TreeNode child = z[i];
            assert (child != null);
            recursiveKey = recursiveKey.appendSpace(context.buildChild(child));
        }

        return Doc.group(
                recursiveKey
        );
    }
}
