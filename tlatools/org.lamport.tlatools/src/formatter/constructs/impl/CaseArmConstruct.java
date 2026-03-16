package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Exmaple: ` 'self="ClientRequest"->"ClientRequestLoop"'`
 *
 */
public class CaseArmConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_CaseArm";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.CASE_ARM.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 3);
        return Doc.group(
                context.buildChild(z[0]) // condition expr
                        .appendSpace(context.buildChild(z[1])) // ->
                        .appendLineOrSpace(context.buildChild(z[2])) // result
        );
    }
}
