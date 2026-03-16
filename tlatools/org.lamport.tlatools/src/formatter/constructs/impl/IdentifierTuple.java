package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

public class IdentifierTuple implements TlaConstruct {
    @Override
    public String getName() {
        return "N_IdentifierTuple";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.IDENTIFIER_TUPLE.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length > 0);
        var d = context.buildChild(z[0]);
        for (int i = 1; i < z.length; i++) {
            if (z[i].getImage().equals(",")) {
                d = d.appendLineOrSpace(context.buildChild(z[i]));
            } else {
                d = d.append(context.buildChild(z[i]));
            }
        }
        return Doc.group(d).indent(indentSize);
    }
}
