package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: the x in `let x in y`.
 */
public class LetDefinitionsConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_LetDefinitions";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.LET_DEFINITIONS.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length > 0);
        var defs = context.buildChild(z[0]);
        for (int i = 1; i < z.length; i++) {
            defs = defs.appendLine(context.buildChild(z[i]));
        }
        return Doc.group(defs);
    }
}
